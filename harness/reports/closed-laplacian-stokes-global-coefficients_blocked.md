# Closed Laplacian Stokes global coefficients: blocked at the intrinsic identity

Date: 2026-09-11. Base: `28c6bb478e20ddcd8049d2baa7e4ad1585b48f42`.
Branch: `worker/closed-laplacian-stokes-global-coefficients`.
Proof head: `1e10431174bd07750ebeddd66f7d43ca6bb7fec6`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

The unconditional `closedLaplacianStokes_of_contMDiff_two` and its unconditional
forward-flow corollary are **not proved or declared**. Item 3 resisted. Items 1
and 2 now have committed theorems: a shrunk finite cover with simultaneous global
smooth coefficient extensions, the genuine density divergence identity in
dimension three, and its transfer to locally agreeing extensions. Item 4 is not
assembled. In particular, the existing full-target constructor cannot consume a
shrunk domain without additional restriction work.

The single new Lean module is
`Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean`, in the requested
namespace. It contains eleven theorems and no new definitions or instances.
Every theorem was compiled and dependency-checked before its individual commit.
The final source compiles without warnings. All eleven declarations print exactly
`[propext, Classical.choice, Quot.sound]`, after normalizing whitespace only.
The forbidden-token scan is empty, exit 1; whitespace checks exit 0.

## Committed results

| Theorem | Result | First proof commit |
| --- | --- | --- |
| `contDiff_cutoff_mul` | Global smoothness of a cutoff times an open-domain smooth field, including the boundary | `fc9c641f` |
| `exists_cutoff_of_isCompact` | Smooth cutoff supported in an open domain, equal to one near every point of a compact subset | `51d21f04` |
| `exists_global_coefficients_on_compact` | Genuine weight and inverse Gram extensions, global smoothness, neighborhood agreement, and density agreement | `97e1acec` |
| `exists_shrunk_chart_cover` | Finite open shrinking, compact coordinate closures inside the targets, and subordinate smooth partition | `602e53b5` |
| `fderiv_chartWeight` | Spatial derivative of the genuine Hausdorff weight in every direction | `3d89675d` |
| `deriv_matrix_inv_entry` | Matrix inverse derivative from differentiating the inverse identity | `fd96c61b` |
| `fderiv_chartInverseMetric` | Spatial derivative of each genuine inverse Gram entry | `e25cb170` |
| `density_inverse_contraction_three` | Finite algebraic contraction for a symmetric three-dimensional inverse matrix | `865e199e` |
| `density_inverseMetric_compatibility` | The full genuine chart divergence identity, with the standard Christoffel coefficient formula | `f6c39b46` |
| `density_inverseMetric_compatibility_of_eventuallyEq` | Transfer of that identity to locally agreeing extended weight and inverse coefficients | `3c3b7cd0` |
| `exists_shrunk_cover_global_coefficients` | Simultaneous coefficient witnesses for the finite shrinking | `db8e9175` |

The final cleanup commit `1e104311` removes unused assumptions from the cover lemma.

## Item 1: finite shrinking and coefficient extensions

For each selected chart, the shrinking theorem gives an open `V i` with
`closure (V i)` inside the genuine source. Their union is the whole manifold.
The image of this closure is compact and contained in the genuine chart target.
A smooth partition is subordinate to the `V i`.

The scalar extension uses multiplication by a smooth cutoff. On the target,
regularity follows from `chartWeight_regular` and `chartInverseMetric_contDiffOn`.
Outside the target, the cutoff vanishes on a neighborhood, so the product is
locally zero. The resulting coefficients are globally infinitely differentiable,
which is stronger than the required C1 regularity. They agree with the genuine
fields on a neighborhood of every point of the compact coordinate closure.
This includes the coordinate images of the partition supports and permits
transfer of first derivatives, not only coefficient values.

The implementation uses the landed smooth Urysohn theorem
`exists_contMDiffMap_zero_one_nhds_of_isClosed` for compact sets. The requested
`CovariantDerivative.exists_blending_cutoff`, `exists_global_chart_metric`, and
`contDiff_blendedChartMetric_scalar` were inspected. Their center-based agreement
is useful for the connection bridge, but the compact-set Urysohn statement fits
arbitrary members of the finite shrinking directly. The genuine coefficient
regularity theorems already use the landed determinant regularity result.

One elaboration hazard was found and corrected: an inverse inside a function
whose expected result is `Fin n → Fin n → ℝ` can select pointwise reciprocal.
The matrix-valued local-agreement expressions now explicitly annotate the result
as `Matrix (Fin n) (Fin n) ℝ`. The verified inverse derivative and compatibility
statements use the genuine nonsingular matrix inverse.

## Item 2: divergence identity proved

The repository already contains Jacobi's formula and the square-root determinant
derivative in `Global/CoordinateVolumeDensityVariation.lean`. The spatial weight
proof applies this result to the line `z + t • v` and uses uniqueness of the
one-variable derivative to identify it with `fderiv`.

The inverse derivative proof differentiates `A(s)⁻¹ * A(s) = 1`, obtains
`Q * A(t) + A(t)⁻¹ * D = 0`, and multiplies by the inverse. It requires only
entrywise differentiability and nonzero determinant. The spatial specialization
uses the established chart regularity. The contraction is proved in dimension
three by expanding finite sums, applying inverse-matrix symmetry, and ring
normalization. No derivative identity is supplied as a premise.

With the genuine `G`, `a = G⁻¹`, weight `w`, and the conventional `Γ`, the
committed theorem proves exactly

```lean
(∑ k : Fin 3,
  fderiv ℝ (fun y ↦ w y * a y k j) z
    (EuclideanSpace.single k (1 : ℝ))) =
  w z * (-(∑ k : Fin 3, ∑ l : Fin 3, a z k l * Γ z j k l))
```

It holds throughout the genuine target. The extension-transfer theorem uses
neighborhood equality and `EventuallyEq.fderiv_eq`, then equality at the base
point. Thus the global extensions satisfy it on the shrunk regions as well.

## Item 3: exact resisting identity

The diagnostic uses a region `V` with closure inside the chart source, a C2
scalar `φ` with `tsupport φ ⊆ V`, and `z` in the coordinate image of `V`.
Its coordinate scalar is globally C2 by the landed theorem, and the new
compatibility theorem is available. The remaining equality is

```lean
g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
  christoffelCoordinateLaplacian a Γ
    (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p φ) z
```

After rewriting with `g.laplacianAt_eq_trace_hessianContinuousAt`, Lean leaves

```lean
(LinearMap.trace ℝ
    (TangentSpace (closedSmoothModelWithCorners 3)
      (inverseExtendedChartParametrization p z)))
  (↑((g.metricBilinAt (inverseExtendedChartParametrization p z)).toDual ⋯).symm ∘ₗ
    ↑LinearMap.toContinuousLinearMap.symm ∘ₗ
      ↑(g.hessianContinuousAt φ (inverseExtendedChartParametrization p z))) =
  christoffelCoordinateLaplacian a Γ
    (ClosedLaplacianStokesProducer.coordinateScalar p φ) ↑z
```

The displayed `⋯` is Lean's suppression of existing proof arguments. The full
actual diagnostic output and its source are below.

`DeTurckPrincipalIdentity.christoffel_eq_connection` identifies the actual
chart Christoffel field with an inverse-metric Koszul expression where the
canonical cutoff is locally one. `koszul_apply` expands that covector. Neither
theorem directly evaluates the intrinsic scalar Hessian or transforms its trace
into the inverse-chart basis. The more general
`LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one`
accepts arbitrary cutoffs with the required smoothness and support. Its signature
was checked successfully. A next proof must apply that bridge to the intrinsic
gradient, identify its coordinate derivative, and transport the metric trace.
No such Hessian-transport theorem is claimed here.

## Constructor and flow boundaries

The task describes agreement near partition supports as sufficient for the
record. The actual record requires agreement at **every point of its chosen
coordinate domain**. The landed `geometry_of_coordinate_coefficients` fixes that
domain to each entire original target. It has no argument for `V` or a smaller
coordinate domain. Its `hweight` and `hcompat` therefore remain full-target
obligations even after choosing a partition with smaller support.

The new extensions provide the correct local data for a record using the image
of `V i` as its coordinate domain. A new restricted-domain constructor must also
supply the restricted chart measure, density integrability, coordinate support,
and localized Laplacian measurability fields. This has not been implemented.
The existing constructor and all frozen definitions remain unchanged. No claim
is made that its five arguments have been discharged as currently quantified.

A successful diagnostic checks the exact definitional equality

```lean
ClosedLaplacianStokes g f =
  (Integrable (fun x ↦ g.laplacianAt f x) (volumeMeasure g) ∧
    (∫ x, g.laplacianAt f x ∂(volumeMeasure g)) = 0)
```

A second successful diagnostic obtains the requested forward-flow conclusion
from an **explicitly assumed** static Stokes theorem. It uses
`scalarAt_contMDiffAt_two_of_normalizedRicciFlow` and
`timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three`.
This checks the corollary step; it does not supply the missing static theorem.
Neither diagnostic adds a declaration to the committed module.

## Review and next action

The initial worktree was clean on the assigned worker branch at the base above.
README, HANDOFF's top section, PROJECT_MAP, the task, producer report, and nearby
source definitions were inspected against the checkout. No existing Lean file,
root import, frozen task, or HANDOFF was edited. Only the requested new Lean
module and this report are added. No full build, root audit, merge, or acceptance
was performed. The report carries the dated handoff because the worker scope
keeps existing files read-only.

First action for independent review:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Then review `git diff 28c6bb47..1e104311 -- Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean`
and rerun all eleven dependency prints. The next theorem-shaped objective is the
Hessian-transport equality displayed above; the next assembly task is a
restricted-domain producer for the original geometry record.

## Diagnostic sources

The following tails are appended inside the module namespace. The resisting
probe additionally imports `Poincare.Global.DeTurckPrincipalIdentity`.

### Intrinsic identity diagnostic

```lean
example
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
    (V : Set M₃) (hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source)
    (φ : M₃ → ℝ) (hφ : tsupport φ ⊆ V)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 φ)
    (z : (extChartAt (closedSmoothModelWithCorners 3) p).target)
    (hz : (z : ClosedSmoothModel 3) ∈ (extChartAt (closedSmoothModelWithCorners 3) p) '' V) :
    let G := inverseChartPullbackGramMatrixField g p
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
    let Γ := fun y j k l ↦ (1 / 2 : ℝ) * ∑ m, a y j m *
      (coordinateDirectionalDerivative (fun q ↦ G q l m) k y +
       coordinateDirectionalDerivative (fun q ↦ G q k m) l y -
       coordinateDirectionalDerivative (fun q ↦ G q k l) m y)
    g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
      christoffelCoordinateLaplacian a Γ
        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p φ) z := by
  intro G a Γ
  have hsource : tsupport φ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source :=
    hφ.trans (subset_closure.trans hV)
  have hu := ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p φ hsource hf
  have hcompat := density_inverseMetric_compatibility g p z z.2
  rw [g.laplacianAt_eq_trace_hessianContinuousAt]
  trace_state

#check DeTurckPrincipalIdentity.christoffel_eq_connection
#check DeTurckPrincipalIdentity.koszul_apply
#check LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
```

### Exact target and conditional flow diagnostic

```lean
example
    (g : ClosedSmoothRiemannianMetric 3 M₃) (f : M₃ → ℝ) :
    ClosedLaplacianStokes g f =
      (Integrable (fun x ↦ g.laplacianAt f x) (volumeMeasure g) ∧
        (∫ x, g.laplacianAt f x ∂(volumeMeasure g)) = 0) := rfl

example
    (hStokes : ∀ (g : ClosedSmoothRiemannianMetric 3 M₃) (f : M₃ → ℝ),
      ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f → ClosedLaplacianStokes g f)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M₃)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M₃, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x) := by
  intro t ht
  apply hStokes
  intro x
  exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow (hFlow t ht)
    (fun y ↦ timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three (hJoint t y)) x

#check ClosedLaplacianStokesProducer.geometry_of_coordinate_coefficients
#check FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes
```

## Actual command output

Compiler failures are retained. Trailing whitespace is removed from transcript
lines for the whitespace gate. Early scratch probes were corrected before any
corresponding theorem was committed.

### Command

```sh
sed -n '465,550p' .lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean; rg -n 'det.*[Dd]eriv|[Dd]eriv.*det|[Dd]eriv.*[Ii]nv' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv .lake/packages/mathlib/Mathlib/Analysis/Matrix | head -75
```

Exit: 0

```text
theorem toSmoothPartitionOfUnity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) :
    fs.toSmoothPartitionOfUnity i x = 0 :=
  fs.toBumpCovering.toPartitionOfUnity_zero_of_zero h

theorem support_toSmoothPartitionOfUnity_subset (i : ι) :
    support (fs.toSmoothPartitionOfUnity i) ⊆ support (fs i) :=
  fs.toBumpCovering.support_toPartitionOfUnity_subset i

theorem IsSubordinate.toSmoothPartitionOfUnity {f : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : f.IsSubordinate U) : f.toSmoothPartitionOfUnity.IsSubordinate fun i => U (f.c i) :=
  h.toBumpCovering.toPartitionOfUnity

theorem sum_toSmoothPartitionOfUnity_eq (x : M) :
    ∑ᶠ i, fs.toSmoothPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - fs i x) :=
  fs.toBumpCovering.sum_toPartitionOfUnity_eq x

end SmoothBumpCovering

variable (I)
variable [FiniteDimensional ℝ E]
variable [IsManifold I ∞ M] {n : ℕ∞}

/-- Given two disjoint closed sets `s, t` in a Hausdorff σ-compact finite-dimensional manifold,
there exists an infinitely smooth function that is equal to `0` on `s` and to `1` on `t`.
See also `exists_contMDiff_zero_iff_one_iff_of_isClosed`, which ensures additionally that
`f` is equal to `0` exactly on `s` and to `1` exactly on `t`. -/
theorem exists_contMDiffMap_zero_one_of_isClosed [T2Space M] [SigmaCompactSpace M] {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc 0 1 := by
  have : ∀ x ∈ t, sᶜ ∈ 𝓝 x := fun x hx => hs.isOpen_compl.mem_nhds (disjoint_right.1 hd hx)
  rcases SmoothBumpCovering.exists_isSubordinate I ht this with ⟨ι, f, hf⟩
  set g := f.toSmoothPartitionOfUnity
  refine
    ⟨⟨_, g.contMDiff_sum.of_le (by simp)⟩, fun x hx => ?_, fun x => g.sum_eq_one, fun x =>
      ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩
  suffices ∀ i, g i x = 0 by simp only [this, ContMDiffMap.coeFn_mk, finsum_zero, Pi.zero_apply]
  refine fun i => f.toSmoothPartitionOfUnity_zero_of_zero ?_
  exact notMem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)

@[deprecated (since := "2025-12-17")]
alias exists_smooth_zero_one_of_isClosed := exists_contMDiffMap_zero_one_of_isClosed

/-- Given two disjoint closed sets `s, t` in a Hausdorff normal σ-compact finite-dimensional
manifold `M`, there exists a smooth function `f : M → [0,1]` that vanishes in a neighbourhood of `s`
and is equal to `1` in a neighbourhood of `t`. -/
theorem exists_contMDiffMap_zero_one_nhds_of_isClosed
    [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
      ∀ x, f x ∈ Icc 0 1 := by
  obtain ⟨u, u_op, hsu, hut⟩ := normal_exists_closure_subset hs ht.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd.symm)
  obtain ⟨v, v_op, htv, hvu⟩ := normal_exists_closure_subset ht isClosed_closure.isOpen_compl
    (subset_compl_comm.mp hut)
  obtain ⟨f, hfu, hfv, hf⟩ := exists_contMDiffMap_zero_one_of_isClosed I isClosed_closure
    isClosed_closure (subset_compl_iff_disjoint_left.mp hvu) (n := n)
  refine ⟨f, ?_, ?_, hf⟩
  · exact eventually_of_mem (mem_of_superset (u_op.mem_nhdsSet.mpr hsu) subset_closure) hfu
  · exact eventually_of_mem (mem_of_superset (v_op.mem_nhdsSet.mpr htv) subset_closure) hfv

@[deprecated (since := "2025-12-17")]
alias exists_smooth_zero_one_nhds_of_isClosed := exists_contMDiffMap_zero_one_nhds_of_isClosed

/-- Given two sets `s, t` in a Hausdorff normal σ-compact finite-dimensional manifold `M`
with `s` open and `s ⊆ interior t`, there is a smooth function `f : M → [0,1]` which is equal to `s`
in a neighbourhood of `s` and has support contained in `t`. -/
theorem exists_contMDiffMap_one_nhds_of_subset_interior
    [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (hd : s ⊆ interior t) :
    ∃ f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x ∉ t, f x = 0) ∧
      ∀ x, f x ∈ Icc 0 1 := by
  rcases exists_contMDiffMap_zero_one_nhds_of_isClosed I isOpen_interior.isClosed_compl hs
    (by rwa [← subset_compl_iff_disjoint_left, compl_compl]) (n := n) with ⟨f, h0, h1, hf⟩
  refine ⟨f, h1, fun x hx ↦ ?_, hf⟩
  exact h0.self_of_nhdsSet _ fun hx' ↦ hx <| interior_subset hx'

@[deprecated (since := "2025-12-17")]
alias exists_smooth_one_nhds_of_subset_interior := exists_contMDiffMap_one_nhds_of_subset_interior

namespace SmoothPartitionOfUnity

/-- A `SmoothPartitionOfUnity` that consists of a single function, uniformly equal to one,
defined as an example for `Inhabited` instance. -/
def single (i : ι) (s : Set M) : SmoothPartitionOfUnity ι I M s :=
  (BumpCovering.single i s).toSmoothPartitionOfUnity fun j => by
    classical
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:17:For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:41:theorem hasStrictDerivAt_inv (hx : x ≠ 0) : HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹) x := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:55:theorem hasDerivAt_inv (x_ne_zero : x ≠ 0) : HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻¹) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:56:  (hasStrictDerivAt_inv x_ne_zero).hasDerivAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:58:theorem hasDerivWithinAt_inv (x_ne_zero : x ≠ 0) (s : Set 𝕜) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:60:  (hasDerivAt_inv x_ne_zero).hasDerivWithinAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:64:    (hasDerivAt_inv H).differentiableAt⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:66:theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:68:  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv_iff.1 (not_not.2 rfl))]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:70:  · exact (hasDerivAt_inv hne).deriv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:73:theorem deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹ :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:74:  funext fun _ => deriv_inv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:76:theorem derivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:78:  rw [DifferentiableAt.derivWithin (differentiableAt_inv x_ne_zero) hxs]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:79:  exact deriv_inv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:81:theorem hasFDerivAt_inv (x_ne_zero : x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:83:  hasDerivAt_inv x_ne_zero
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:85:theorem hasStrictFDerivAt_inv (x_ne_zero : x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:87:  hasStrictDerivAt_inv x_ne_zero
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:89:theorem hasFDerivWithinAt_inv (x_ne_zero : x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:91:  (hasFDerivAt_inv x_ne_zero).hasFDerivWithinAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:93:theorem fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:94:  rw [← toSpanSingleton_deriv, deriv_inv]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:96:theorem fderivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:98:  rw [DifferentiableAt.fderivWithin (differentiableAt_inv x_ne_zero) hxs]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:99:  exact fderiv_inv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:104:theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:106:  convert (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:110:theorem HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:115:theorem derivWithin_fun_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:118:  · exact (hc.hasDerivWithinAt.inv hx).derivWithin hsx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:121:theorem derivWithin_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:123:  derivWithin_fun_inv' hc hx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:126:theorem deriv_fun_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:128:  (hc.hasDerivAt.inv hx).deriv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:131:theorem deriv_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:133:  (hc.hasDerivAt.inv hx).deriv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:146:  convert hc.fun_mul ((hasDerivAt_inv hx).comp_hasDerivWithinAt x hd) using 1
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:158:  convert hc.fun_mul ((hasStrictDerivAt_inv hx).comp x hd) using 1
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Affine.lean:16:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:14:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:19:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:144:    convert (hd.hasFDerivAt.hasFDerivAt_norm_smul (inv_ne_zero ht)).differentiableAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Star.lean:18:star operation. For detailed documentation of the Fréchet derivative, see the module docstring of
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:15:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:13:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:13:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:13:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:36:  point `f.symm a`, with invertible derivative, then its inverse is analytic at `a`.
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:412:derivative, then its inverse is analytic at `a`. -/
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:15:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:108:theorem fderivWithin_const_smul_of_invertible (c : R) [Invertible c]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:134:theorem fderiv_const_smul_of_invertible (c : R) [Invertible c] :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:136:  simp [← fderivWithin_univ, fderivWithin_const_smul_of_invertible c uniqueDiffWithinAt_univ]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:145:/-- Special case of `fderivWithin_const_smul_of_invertible` over a division semiring: any constant
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:155:    simp [fderivWithin_const_smul_of_invertible c hs]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:173:/-- Special case of `fderiv_const_smul_of_invertible` over a division semiring: any constant is
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:349:    (hf : (fderivWithin 𝕜 f s x).IsInvertible) : DifferentiableWithinAt 𝕜 f s x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:353:    (hf : (fderiv 𝕜 f x).IsInvertible) : DifferentiableAt 𝕜 f x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:14:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:15:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:21:We also prove the usual formula for the derivative of the inverse function, assuming it exists.
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:330:theorem HasFDerivWithinAt.of_local_left_inverse {g : F → E} {f' : E ≃L[𝕜] F} {a : F} {t : Set F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:353:theorem HasStrictFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:379:theorem HasFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:18:For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:23:derivative, inverse function
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:56:theorem HasStrictDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:59:  (hf.hasStrictFDerivAt_equiv hf').of_local_left_inverse hg hfg
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:77:theorem HasDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:80:  (hf.hasFDerivAt_equiv hf').of_local_left_inverse hg hfg
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:15:For detailed documentation of the Fréchet derivative,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:655:/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:661:theorem hasFDerivAt_ringInverse (x : Rˣ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:662:    HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
```

### Command

```sh
rg -n 'exists_isOpen.*|isOpen.*preimage.*continuousOn|isOpen_preimage' .lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean .lake/packages/mathlib/Mathlib/Topology/Separation/Regular.lean .lake/packages/mathlib/Mathlib/Topology/Defs/Filter.lean | head -55; sed -n '210,251p' .lake/packages/mathlib/Mathlib/Topology/ShrinkingLemma.lean; rg -n 'ContDiffOn.*mul.*tsupport|mul.*of_tsupport' .lake/packages/mathlib/Mathlib/Analysis/Calculus
```

Exit: 1

```text
.lake/packages/mathlib/Mathlib/Topology/Separation/Regular.lean:190:theorem IsCompact.exists_isOpen_closure_subset {K U : Set X} (hK : IsCompact K) (hU : U ∈ 𝓝ˢ K) :
.lake/packages/mathlib/Mathlib/Topology/Separation/Regular.lean:203:  rcases hK.exists_isOpen_closure_subset hU with ⟨V, hVo, hKV, hVU⟩
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:184:theorem ContinuousOn.isOpen_preimage {t : Set β} (h : ContinuousOn f s)

variable {u : ι → Set X} {s : Set X} [NormalSpace X]

/-- **Shrinking lemma**. A point-finite open cover of a closed subset of a normal space can be
"shrunk" to a new open cover so that the closure of each new open set is contained in the
corresponding original open set. -/
theorem exists_subset_iUnion_closure_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i := by
  haveI : Nonempty (PartialRefinement u s ⊤) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : ∀ c : Set (PartialRefinement u s ⊤),
      IsChain (· ≤ ·) c → c.Nonempty → ∃ ub, ∀ v ∈ c, v ≤ ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices ∀ i, i ∈ v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i)⟩
  intro i; by_contra hi
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩
  exact hv.not_lt hlt

/-- **Shrinking lemma**. A point-finite open cover of a closed subset of a normal space can be
"shrunk" to a new closed cover so that each new closed set is contained in the corresponding
original open set. See also `exists_subset_iUnion_closure_subset` for a stronger statement. -/
theorem exists_subset_iUnion_closed_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset hs uo uf us
  ⟨fun i => closure (v i), Subset.trans hsv (iUnion_mono fun _ => subset_closure),
    fun _ => isClosed_closure, hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
theorem exists_iUnion_eq_closure_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : ⋃ i, u i = univ) :
    ∃ v : ι → Set X, iUnion v = univ ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_iUnion_closure_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each of the new closed sets is contained in the corresponding
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/inspect.lean
```

Exit: 0

```text
def Poincare.ClosedLaplacianStokes.{u} : {n : ℕ} →
  {M : Type u} →
    [inst : TopologicalSpace M] →
      [T2Space M] →
        [CompactSpace M] →
          [ConnectedSpace M] →
            [inst_4 : MeasurableSpace M] →
              [BorelSpace M] →
                [inst_6 : ChartedSpace (Poincare.ClosedSmoothModel n) M] →
                  [inst_7 : IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M] →
                    Poincare.ClosedSmoothRiemannianMetric n M → (M → ℝ) → Prop :=
fun {n} {M} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M] g f =>
  MeasureTheory.Integrable (fun x => g.laplacianAt f x) (Poincare.volumeMeasure g) ∧
    ∫ (x : M), g.laplacianAt f x ∂Poincare.volumeMeasure g = 0
exists_contMDiffMap_zero_one_nhds_of_isClosed.{uE, uH, uM} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] {n : ℕ∞} [T2Space M] [NormalSpace M] [SigmaCompactSpace M] {s t : Set M}
  (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
  ∃ f, (∀ᶠ (x : M) in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ (x : M) in 𝓝ˢ t, f x = 1) ∧ ∀ (x : M), f x ∈ Set.Icc 0 1
ContMDiff.contDiff.{u_1, u_2, u_5} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type u_5} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {n : ℕ∞ω} {f : E → E'} :
  ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f → ContDiff 𝕜 n f
Filter.Eventually.filter_mono.{u} {α : Type u} {f₁ f₂ : Filter α} (h : f₁ ≤ f₂) {p : α → Prop}
  (hp : ∀ᶠ (x : α) in f₂, p x) : ∀ᶠ (x : α) in f₁, p x
nhds_le_nhdsSet.{u_1} {X : Type u_1} [TopologicalSpace X] {s : Set X} {x : X} (h : x ∈ s) : 𝓝 x ≤ 𝓝ˢ s
notMem_tsupport_iff_eventuallyEq.{u_2, u_4} {α : Type u_2} {β : Type u_4} [TopologicalSpace α] [Zero β] {f : α → β}
  {x : α} : x ∉ tsupport f ↔ f =ᶠ[𝓝 x] 0
ContinuousOn.isOpen_preimage.{u_1, u_2} {α : Type u_1} {β : Type u_2} [TopologicalSpace α] [TopologicalSpace β]
  {f : α → β} {s : Set α} {t : Set β} (h : ContinuousOn f s) (hs : IsOpen s) (hp : f ⁻¹' t ⊆ s) (ht : IsOpen t) :
  IsOpen (f ⁻¹' t)
exists_iUnion_eq_closure_subset.{u_1, u_2} {ι : Type u_1} {X : Type u_2} [TopologicalSpace X] {u : ι → Set X}
  [NormalSpace X] (uo : ∀ (i : ι), IsOpen (u i)) (uf : ∀ (x : X), {i | x ∈ u i}.Finite) (uU : ⋃ i, u i = Set.univ) :
  ∃ v, Set.iUnion v = Set.univ ∧ (∀ (i : ι), IsOpen (v i)) ∧ ∀ (i : ι), closure (v i) ⊆ u i
IsCompact.exists_isOpen_closure_subset.{u_1} {X : Type u_1} [TopologicalSpace X] [RegularSpace X] {K U : Set X}
  (hK : IsCompact K) (hU : U ∈ 𝓝ˢ K) : ∃ V, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U
isOpen_extChartAt_target.{u_1, u_2, u_3, u_4} {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Type u_4}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [I.Boundaryless] (x : M) : IsOpen (extChartAt I x).target
IsOpen.mem_nhdsSet.{u_1} {X : Type u_1} [TopologicalSpace X] {s t : Set X} (hU : IsOpen s) : s ∈ 𝓝ˢ t ↔ t ⊆ s
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:22:2: error: unsolved goals
case h
n : ℕ
U : Set E
χ F : E → ℝ
hU : IsOpen U
hχ : ContDiff ℝ ∞ χ
hχU : tsupport χ ⊆ U
hF : ContDiffOn ℝ ∞ F U
z : E
hz : z ∉ U
hzero : χ =ᶠ[𝓝 z] 0
y : E
hy : χ y = 0 y
⊢ 0 y * F y = ?m.131

n : ℕ
U : Set E
χ F : E → ℝ
hU : IsOpen U
hχ : ContDiff ℝ ∞ χ
hχU : tsupport χ ⊆ U
hF : ContDiffOn ℝ ∞ F U
z : E
hz : z ∉ U
hzero : χ =ᶠ[𝓝 z] 0
⊢ ℝ
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:25:19: warning: This simp argument is unused:
  zero_mul

Hint: Omit it from the simp argument list.
  simp only [hy,̵ ̵z̵e̵r̵o̵_̵m̵u̵l̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-1.lean
```

Exit: 1

```text
/tmp/stokes-global-evidence/dependencies-1.lean:22:2: error: unsolved goals
case h
n : ℕ
U : Set E
χ F : E → ℝ
hU : IsOpen U
hχ : ContDiff ℝ ∞ χ
hχU : tsupport χ ⊆ U
hF : ContDiffOn ℝ ∞ F U
z : E
hz : z ∉ U
hzero : χ =ᶠ[𝓝 z] 0
y : E
hy : χ y = 0 y
⊢ 0 y * F y = ?m.131

n : ℕ
U : Set E
χ F : E → ℝ
hU : IsOpen U
hχ : ContDiff ℝ ∞ χ
hχU : tsupport χ ⊆ U
hF : ContDiffOn ℝ ∞ F U
z : E
hz : z ∉ U
hzero : χ =ᶠ[𝓝 z] 0
⊢ ℝ
/tmp/stokes-global-evidence/dependencies-1.lean:25:19: warning: This simp argument is unused:
  zero_mul

Hint: Omit it from the simp argument list.
  simp only [hy,̵ ̵z̵e̵r̵o̵_̵m̵u̵l̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, zero_mul]

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
```

### Command

```sh
rg -n 'contDiffAt_const|contDiff_iff_contDiffAt|ContDiffAt.congr_of_eventuallyEq|ContDiffWithinAt.contDiffAt|nhds_le_nhdsSet|notMem_tsupport_iff_eventuallyEq' .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean .lake/packages/mathlib/Mathlib/Topology/NhdsSet.lean | head -35
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Topology/NhdsSet.lean:147:theorem nhds_le_nhdsSet (h : x ∈ s) : 𝓝 x ≤ 𝓝ˢ s :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:941:theorem ContDiffWithinAt.contDiffAt (h : ContDiffWithinAt 𝕜 n f s x) (hx : s ∈ 𝓝 x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:957:theorem ContDiffAt.congr_of_eventuallyEq (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1094:theorem contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ ∀ x, ContDiffAt 𝕜 n f x := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1099:  contDiff_iff_contDiffAt.1 h x
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-1.lean
```

Exit: 0

```text
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Extend chartwise smooth scalars by cutoff multiplication"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients fc9c641f] Extend chartwise smooth scalars by cutoff multiplication
 1 file changed, 27 insertions(+)
 create mode 100644 Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
```

### Command

```sh
rg -n 'hasFDerivAt_det|hasDerivAt_det|deriv_det|fderiv_det|hasFDerivAt.*[Dd]et|jacobi' .lake/packages/mathlib/Mathlib Poincare/VolumeDensity.lean; rg -n 'disjoint_compl_left_iff_subset|contDiffAt_const' .lake/packages/mathlib/Mathlib/Order .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff | head -20
```

Exit: 0

```text
rg: Poincare/VolumeDensity.lean: No such file or directory (os error 2)
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:49:lie bracket, jacobi identity, lie ring, lie algebra, lie module
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:229:theorem lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:17:We define the Jacobi symbol, `jacobiSym a b`, for integers `a` and natural numbers `b`
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:22:this implies in particular that `jacobiSym a 0 = 1` for all `a`.
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:28:* Multiplicativity in both arguments (`jacobiSym.mul_left`, `jacobiSym.mul_right`)
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:31:  (`jacobiSym.eq_one_or_neg_one`)
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:34:  (`jacobiSym.eq_zero_iff_not_coprime`)
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:37:  (`ZMod.nonsquare_of_jacobiSym_eq_neg_one`); the converse holds when `b = p` is a prime
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:38:  (`ZMod.nonsquare_iff_jacobiSym_eq_neg_one`); in particular, in this case `a` is a
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:39:  square mod `p` when the symbol has the value `1` (`ZMod.isSquare_of_jacobiSym_eq_one`).
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:41:* Quadratic reciprocity (`jacobiSym.quadratic_reciprocity`,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:42:  `jacobiSym.quadratic_reciprocity_one_mod_four`,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:43:  `jacobiSym.quadratic_reciprocity_three_mod_four`)
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:45:* The supplementary laws for `a = -1`, `a = 2`, `a = -2` (`jacobiSym.at_neg_one`,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:46:  `jacobiSym.at_two`, `jacobiSym.at_neg_two`)
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:48:* The symbol depends on `a` only via its residue class mod `b` (`jacobiSym.mod_left`)
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:49:  and on `b` only via its residue class mod `4*a` (`jacobiSym.mod_right`)
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:51:* A `csimp` rule for `jacobiSym` and `legendreSym` that evaluates `J(a | b)` efficiently by
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:57:We define the notation `J(a | b)` for `jacobiSym a b`, localized to `NumberTheorySymbols`.
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:75:is `1` when `b = 0`). This is called `jacobiSym a b`.
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:78:symbol `jacobiSym a b`.
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:86:def jacobiSym (a : ℤ) (b : ℕ) : ℤ :=
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:92:scoped[NumberTheorySymbols] notation "J(" a " | " b ")" => jacobiSym a b
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:101:namespace jacobiSym
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:106:  simp only [jacobiSym, primeFactorsList_zero, List.prod_nil, List.pmap]
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:111:  simp only [jacobiSym, primeFactorsList_one, List.prod_nil, List.pmap]
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:115:theorem legendreSym.to_jacobiSym (p : ℕ) [fp : Fact p.Prime] (a : ℤ) :
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:117:  simp only [jacobiSym, primeFactorsList_prime fp.1, List.prod_cons, List.prod_nil, mul_one,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:123:  rw [jacobiSym, ((perm_primeFactorsList_mul hb₁ hb₂).pmap _).prod_eq, List.pmap_append,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:155:  simp_rw [jacobiSym, List.pmap_eq_map_attach, legendreSym.mul _ _ _]
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:181:    exact ⟨hb, mt jacobiSym.ne_zero <| Classical.not_not.2 h⟩, fun ⟨hb, h⟩ => by
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:191:  (trichotomy a b).resolve_left <| jacobiSym.ne_zero h
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:232:  rw [← legendreSym.to_jacobiSym] at h
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:267:end jacobiSym
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:271:open jacobiSym
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:274:theorem nonsquare_of_jacobiSym_eq_neg_one {a : ℤ} {b : ℕ} (h : J(a | b) = -1) :
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:282:theorem nonsquare_iff_jacobiSym_eq_neg_one {a : ℤ} {p : ℕ} [Fact p.Prime] :
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:284:  rw [← legendreSym.to_jacobiSym]
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:288:theorem isSquare_of_jacobiSym_eq_one {a : ℤ} {p : ℕ} [Fact p.Prime] (h : J(a | p) = 1) :
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:290:  Classical.not_not.mp <| by rw [← nonsquare_iff_jacobiSym_eq_neg_one, h]; decide
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:299:namespace jacobiSym
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:307:  rw [jacobiSym, List.map_map, ← List.pmap_eq_map
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:336:  rw [Int.mul_ediv_cancel_left _ (by decide), jacobiSym.mul_left,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:337:    (by decide : (4 : ℤ) = (2 : ℕ) ^ 2), jacobiSym.sq_one' this, one_mul]
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:348:  rw [Int.mul_ediv_cancel_left _ (by decide), jacobiSym.mul_left,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:349:    jacobiSym.at_two (Nat.odd_iff.mpr hb2), ZMod.χ₈_nat_eq_if_mod_eight,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:353:end jacobiSym
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:371:  · rw [χ₄_nat_one_mod_four h, jacobiSym.one_left, one_pow]
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:372:  · rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (odd_iff.mp hn), jacobiSym.at_neg_one hn]
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:380:  simp_rw [qrSign, Nat.cast_mul, map_mul, jacobiSym.mul_left]
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:385:  jacobiSym.mul_right (χ₄ m) n₁ n₂
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:403:namespace jacobiSym
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:417:  rw [@legendreSym.to_jacobiSym p ⟨pp⟩, rhs_apply, Nat.cast_id, qrSign.eq_iff_eq hpo ha,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:421:  rw [rhs_apply, Nat.cast_id, ← @legendreSym.to_jacobiSym p ⟨pp⟩, qrSign.symm hqo hpo,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:453:  · simpa [ha1] using jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hb2) ha1
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:455:  · simpa [hb1] using jacobiSym.quadratic_reciprocity_one_mod_four hb1 (Nat.odd_iff.mpr ha2)
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:456:  simpa [ha3, hb3] using (jacobiSym.quadratic_reciprocity_three_mod_four ha3 hb3).symm
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:485:    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', mod_right' _ hb, χ₄_nat_mod_four,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:488:end jacobiSym
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:502:open NumberTheorySymbols jacobiSym
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:525:private theorem fastJacobiSymAux.eq_jacobiSym {a b : ℕ} {flip : Bool} {ha0 : a > 0}
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:568:@[csimp] private theorem fastJacobiSym.eq : jacobiSym = fastJacobiSym := by
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:586:  · rw [fastJacobiSymAux.eq_jacobiSym, if_neg Bool.false_ne_true, mod_left a b,
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:598:  ext p _ a; rw [legendreSym.to_jacobiSym, fastLegendreSym]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:231:lemma exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:234:        P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:235:  have H : P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 ∈ P.ker := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:236:    simp [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:239:/-- An arbitrarily chosen relation exhibiting the fact that `P.jacobian` is invertible. -/
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:241:def jacobianRelations (s : σ) : MvPolynomial ι R :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:244:  P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose s
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:246:lemma jacobianRelations_spec [DecidableEq σ] [Fintype σ] :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:247:    ∑ i, P.jacobianRelations i * P.relation i =
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:248:      P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:249:  delta jacobianRelations
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:250:  convert P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose_spec
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:254:  P.toPresentation.coeffs ∪ (P.σ (P.jacobian_isUnit.unit⁻¹ :)).coeffs ∪
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:255:    ⋃ i, (P.jacobianRelations i).coeffs
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:276:/-- The jacobian of a presentation in the smaller coefficient ring, provided `P.HasCoeffs R₀`. -/
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:278:def jacobianOfHasCoeffs : MvPolynomial ι R₀ :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:281:  (P.toPreSubmersivePresentation.ofHasCoeffs R₀).jacobiMatrix.det
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:284:lemma map_jacobianOfHasCoeffs [Fintype σ] [DecidableEq σ] :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:285:    (P.jacobianOfHasCoeffs R₀).map (algebraMap R₀ R) = P.jacobiMatrix.det := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:286:  rw [jacobianOfHasCoeffs, @RingHom.map_det]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:290:    PreSubmersivePresentation.jacobiMatrix_apply]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:293:lemma aeval_jacobianOfHasCoeffs :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:294:    MvPolynomial.aeval P.val (P.jacobianOfHasCoeffs R₀) = P.jacobian := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:297:  rw [← MvPolynomial.aeval_map_algebraMap R, map_jacobianOfHasCoeffs,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:298:    P.jacobian_eq_jacobiMatrix_det, Generators.algebraMap_apply]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:300:/-- The inverse jacobian of a presentation in the smaller coefficient ring,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:310:    (P.invJacobianOfHasCoeffs R₀).map (algebraMap R₀ R) = P.σ ↑(P.jacobian_isUnit.unit⁻¹) :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:317:    MvPolynomial.aeval P.val (P.invJacobianOfHasCoeffs R₀) = ↑(P.jacobian_isUnit.unit⁻¹) := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:321:/-- An arbitrarily chosen relation exhibiting the fact that `P.jacobian` is invertible,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:324:def jacobianRelationsOfHasCoeffs (i : σ) : MvPolynomial ι R₀ :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:330:lemma map_jacobianRelationsOfHasCoeffs (i : σ) :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:331:    (P.jacobianRelationsOfHasCoeffs R₀ i).map (algebraMap R₀ R) = P.jacobianRelations i :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:336:lemma sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs [FaithfulSMul R₀ R] [Fintype σ] :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:337:    ∑ i, P.jacobianRelationsOfHasCoeffs R₀ i * P.relationOfHasCoeffs R₀ i =
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:338:      P.jacobianOfHasCoeffs R₀ * P.invJacobianOfHasCoeffs R₀ - 1 := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:341:  simp [P.map_relationOfHasCoeffs, jacobianRelations_spec]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:349:  jacobian_isUnit := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:353:      $(P.sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs R₀))
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:357:    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Core.lean:358:    simp [jacobianOfHasCoeffs]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:37:- `PreSubmersivePresentation.jacobian`: The determinant of `P.differential`.
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:38:- `PreSubmersivePresentation.jacobiMatrix`: If `σ` has a `Fintype` instance, we may form
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:39:  the matrix corresponding to `P.differential`. Its determinant is `P.jacobian`.
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:100:is submersive. See `PreSubmersivePresentation.jacobian`.
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:119:noncomputable def jacobian : S :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:132:noncomputable def jacobiMatrix : Matrix σ σ P.Ring :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:135:lemma jacobian_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:136:  simp [jacobiMatrix, jacobian]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:138:lemma jacobiMatrix_apply (i j : σ) :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:139:    P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j) := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:140:  simp [jacobiMatrix, LinearMap.toMatrix, differential, basis]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:142:lemma aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:143:    P.aevalDifferential.toMatrix' = (aeval P.val).mapMatrix P.jacobiMatrix := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:147:  simp [jacobiMatrix_apply]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:155:lemma jacobian_eq_det_aevalDifferential : P.jacobian = P.aevalDifferential.det := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:158:  simp [← LinearMap.det_toMatrix', P.aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:159:    jacobian_eq_jacobiMatrix_det, RingHom.map_det, P.algebraMap_eq]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:161:lemma isUnit_jacobian_iff_aevalDifferential_bijective :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:162:    IsUnit P.jacobian ↔ Function.Bijective P.aevalDifferential := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:163:  rw [P.jacobian_eq_det_aevalDifferential, ← LinearMap.isUnit_iff_isUnit_det]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:166:lemma isUnit_jacobian_of_linearIndependent_of_span_eq_top
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:170:    IsUnit P.jacobian := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:172:  rw [isUnit_jacobian_iff_aevalDifferential_bijective]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:190:lemma jacobiMatrix_ofAlgEquiv (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:192:    (P.ofAlgEquiv e).jacobiMatrix = P.jacobiMatrix :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:197:lemma jacobian_ofAlgEquiv (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:199:    (P.ofAlgEquiv e).jacobian = e P.jacobian := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:202:  rw [jacobian_eq_jacobiMatrix_det, jacobian_eq_jacobiMatrix_det]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:204:    jacobiMatrix_ofAlgEquiv, Generators.algebraMap_apply, Generators.ofAlgEquiv_val,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:217:lemma ofBijectiveAlgebraMap_jacobian (h : Function.Bijective (algebraMap R S)) :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:218:    (ofBijectiveAlgebraMap h).jacobian = 1 := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:221:      (ofBijectiveAlgebraMap h).jacobiMatrix = 1 := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:224:  rw [jacobian_eq_jacobiMatrix_det, RingHom.map_det, this, Matrix.det_one]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:240:lemma localizationAway_jacobiMatrix :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:241:    (localizationAway S r).jacobiMatrix = Matrix.diagonal (fun () ↦ MvPolynomial.C r) := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:244:  rwa [jacobiMatrix_apply]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:247:lemma localizationAway_jacobian : (localizationAway S r).jacobian = algebraMap R S r := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:248:  rw [jacobian_eq_jacobiMatrix_det, localizationAway_jacobiMatrix]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:300:private lemma jacobiMatrix_comp_inl_inr (i : σ') (j : σ) :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:301:    (Q.comp P).jacobiMatrix (Sum.inl i) (Sum.inr j) = 0 := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:303:  rw [jacobiMatrix_apply]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:309:private lemma jacobiMatrix_comp_₁₂ : (Q.comp P).jacobiMatrix.toBlocks₁₂ = 0 := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:311:  simp [Matrix.toBlocks₁₂, jacobiMatrix_comp_inl_inr]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:316:private lemma jacobiMatrix_comp_inl_inl (i j : σ') :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:318:      ((Q.comp P).jacobiMatrix (Sum.inl j) (Sum.inl i)) = Q.jacobiMatrix j i := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:319:  rw [jacobiMatrix_apply, jacobiMatrix_apply, comp_map, Sum.elim_inl,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:324:private lemma jacobiMatrix_comp_₁₁_det :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:325:    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det = Q.jacobian := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:326:  rw [jacobian_eq_jacobiMatrix_det, AlgHom.map_det (aeval (Q.comp P).val), RingHom.map_det]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:329:  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, ← Q.jacobiMatrix_comp_inl_inl P,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:338:private lemma jacobiMatrix_comp_inr_inr (i j : σ) :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:339:    (Q.comp P).jacobiMatrix (Sum.inr i) (Sum.inr j) =
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:340:      MvPolynomial.rename Sum.inr (P.jacobiMatrix i j) := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:341:  rw [jacobiMatrix_apply, jacobiMatrix_apply]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:346:private lemma jacobiMatrix_comp_₂₂_det :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:347:    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = algebraMap S T P.jacobian := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:348:  rw [jacobian_eq_jacobiMatrix_det]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:354:  rw [jacobiMatrix_comp_inr_inr, ← IsScalarTower.algebraMap_eq]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:356:  generalize P.jacobiMatrix i j = p
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:371:lemma comp_jacobian_eq_jacobian_smul_jacobian [Finite σ] [Finite σ'] :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:372:    (Q.comp P).jacobian = P.jacobian • Q.jacobian := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:376:  rw [jacobian_eq_jacobiMatrix_det, ← Matrix.fromBlocks_toBlocks ((Q.comp P).jacobiMatrix),
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:377:    jacobiMatrix_comp_₁₂]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:379:    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det *
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:380:    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = P.jacobian • Q.jacobian
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:383:    convert Matrix.det_fromBlocks_zero₁₂ (Q.comp P).jacobiMatrix.toBlocks₁₁
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:384:      (Q.comp P).jacobiMatrix.toBlocks₂₁ (Q.comp P).jacobiMatrix.toBlocks₂₂
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:385:  · rw [jacobiMatrix_comp_₁₁_det, jacobiMatrix_comp_₂₂_det, mul_comm, Algebra.smul_def]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:407:lemma baseChange_jacobian [Finite σ] : (P.baseChange T).jacobian = 1 ⊗ₜ P.jacobian := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:410:  simp_rw [jacobian_eq_jacobiMatrix_det]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:411:  have h : (baseChange T P).jacobiMatrix =
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:412:      (MvPolynomial.map (algebraMap R T)).mapMatrix P.jacobiMatrix := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:414:    simp only [baseChange, jacobiMatrix_apply, Presentation.baseChange_relation,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:435:lemma jacobiMatrix_reindex {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ)
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:437:    (P.reindex e f).jacobiMatrix =
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:438:      (P.jacobiMatrix.reindex f.symm f.symm).map (MvPolynomial.rename e.symm) := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:440:  simp [jacobiMatrix_apply,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:445:lemma jacobian_reindex (P : PreSubmersivePresentation R S ι σ)
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:447:    (P.reindex e f).jacobian = P.jacobian := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:451:  simp_rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:452:  simp only [reindex_toPresentation, Presentation.reindex_toGenerators, jacobiMatrix_reindex,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:470:`PreSubmersivePresentation.jacobiMatrix_naive`.
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:483:@[simp] lemma jacobiMatrix_naive [Fintype ι] [DecidableEq ι] (i j : ι) :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:484:    (naive a ha s hs).jacobiMatrix i j = (v j).pderiv (a i) :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:485:  jacobiMatrix_apply _ _ _
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:501:  jacobian_isUnit : IsUnit toPreSubmersivePresentation.jacobian
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:516:  jacobian_isUnit := by simp [P.jacobian_isUnit]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:524:  jacobian_isUnit := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:525:    rw [ofBijectiveAlgebraMap_jacobian]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:541:  jacobian_isUnit := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:542:    rw [comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def, IsUnit.mul_iff]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:543:    exact ⟨RingHom.isUnit_map _ <| P.jacobian_isUnit, Q.jacobian_isUnit⟩
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:555:  jacobian_isUnit := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:556:    rw [localizationAway_jacobian]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:570:  jacobian_isUnit :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:571:    P.baseChange_jacobian T ▸ P.jacobian_isUnit.map TensorProduct.includeRight
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:583:  jacobian_isUnit := by simp [P.jacobian_isUnit]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:597:  jacobian_isUnit := isUnit_of_subsingleton _
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:610:    convert P.jacobian_isUnit
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:611:    rw [LinearMap.toMatrix_eq_toMatrix', jacobian_eq_jacobiMatrix_det,
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:612:      aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix, P.algebraMap_eq]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Cotangent/Free.lean:24:- `PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective`:
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Cotangent/Free.lean:53:Via `PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective`, this can be useful
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Cotangent/Free.lean:117:lemma isUnit_jacobian_of_cotangentRestrict_bijective
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Cotangent/Free.lean:121:    IsUnit P.jacobian := by
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Cotangent/Free.lean:126:  apply P.isUnit_jacobian_of_linearIndependent_of_span_eq_top
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:52:See `jacobiSym.at_two` and `jacobiSym.at_neg_two` for the corresponding statements
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:94:See `jacobiSym.quadratic_reciprocity` and variants for a version of Quadratic Reciprocity
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/Basic.lean:19:The Legendre symbol is used to define the Jacobi symbol, `jacobiSym a b`, for integers `a`
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/Basic.lean:265:See `jacobiSym.at_neg_one` for the corresponding statement for the Jacobi symbol.
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:60:/-- Variant of `jacobiTheta₂'` which we introduce to simplify some formulae. -/
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:61:def jacobiTheta₂'' (z τ : ℂ) : ℂ :=
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:62:  cexp (π * I * z ^ 2 * τ) * (jacobiTheta₂' (z * τ) τ / (2 * π * I) + z * jacobiTheta₂ (z * τ) τ)
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:64:lemma jacobiTheta₂''_conj (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:65:    conj (jacobiTheta₂'' z τ) = jacobiTheta₂'' (conj z) (-conj τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:66:  simp [jacobiTheta₂'', jacobiTheta₂'_conj, jacobiTheta₂_conj, ← exp_conj, map_ofNat, div_neg,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:67:    neg_div, jacobiTheta₂'_neg_left]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:69:/-- Restatement of `jacobiTheta₂'_add_left'`: the function `jacobiTheta₂''` is 1-periodic in `z`. -/
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:70:lemma jacobiTheta₂''_add_left (z τ : ℂ) : jacobiTheta₂'' (z + 1) τ = jacobiTheta₂'' z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:71:  simp only [jacobiTheta₂'', add_mul z 1, one_mul, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:72:  generalize jacobiTheta₂ (z * τ) τ = J
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:73:  generalize jacobiTheta₂' (z * τ) τ = J'
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:82:lemma jacobiTheta₂''_neg_left (z τ : ℂ) : jacobiTheta₂'' (-z) τ = -jacobiTheta₂'' z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:83:  simp [jacobiTheta₂'', jacobiTheta₂'_neg_left, neg_div, -neg_add_rev, ← neg_add]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:85:lemma jacobiTheta₂'_functional_equation' (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:86:    jacobiTheta₂' z τ = (-2 * π) / (-I * τ) ^ (3 / 2 : ℂ) * jacobiTheta₂'' z (-1 / τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:88:  · rw [jacobiTheta₂'_undef _ (by simp), mul_zero, zero_cpow (by simp), div_zero, zero_mul]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:92:  rw [jacobiTheta₂'_functional_equation, ← mul_one_div _ τ, mul_right_comm _ (cexp _),
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:99:  rw [jacobiTheta₂'', div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc, ← mul_div_assoc,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:101:    jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left, neg_mul, ← mul_neg, ← mul_neg,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:111:  (show Function.Periodic (fun a : ℝ ↦ re (jacobiTheta₂'' a (I * x))) 1 by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:112:    simp [jacobiTheta₂''_add_left]).lift a
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:114:lemma oddKernel_def (a x : ℝ) : ↑(oddKernel a x) = jacobiTheta₂'' a (I * x) := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:115:  simp [oddKernel, ← conj_eq_iff_re, jacobiTheta₂''_conj]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:118:    (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) (I * x)) := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:119:  rw [oddKernel_def, jacobiTheta₂'', ← mul_assoc ↑a I x,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:124:  rw [← ofReal_eq_zero, oddKernel_def', jacobiTheta₂_undef, jacobiTheta₂'_undef, zero_div, zero_add,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:132:  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂' ξ (I * x) / (-2 * π))) 1 by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:133:    simp [jacobiTheta₂'_add_left]).lift a
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:135:lemma sinKernel_def (a x : ℝ) : ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π) := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:136:  simp [sinKernel, re_eq_add_conj, jacobiTheta₂'_conj, map_ofNat]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:140:  | H a => rw [← ofReal_eq_zero, sinKernel_def, jacobiTheta₂'_undef _ (by simpa), zero_div]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:144:  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, oddKernel_def, jacobiTheta₂''_neg_left]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:152:  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, sinKernel_def, jacobiTheta₂'_neg_left,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:168:    · exact ((continuousAt_jacobiTheta₂' (a * I * x) (by rwa [I_mul_im, ofReal_re])).comp
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:170:    · exact continuousAt_const.mul <| (continuousAt_jacobiTheta₂ (a * I * x)
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:179:  have h := continuousAt_jacobiTheta₂' a (by rwa [I_mul_im, ofReal_re])
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:195:  rw [← ofReal_inj, oddKernel_def, ofReal_mul, sinKernel_def, jacobiTheta₂'_functional_equation',
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:197:  generalize jacobiTheta₂'' a (I * ↑x) = J
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:214:  have h1 := hasSum_jacobiTheta₂_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:215:  have h2 := hasSum_jacobiTheta₂'_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:218:  rw [jacobiTheta₂'_term, mul_assoc (2 * π * I), mul_div_cancel_left₀ _ two_pi_I_ne_zero, ← add_mul,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:219:    mul_left_comm, jacobiTheta₂_term, ← Complex.exp_add]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:232:  refine ((hasSum_jacobiTheta₂'_term a
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean:234:  rw [jacobiTheta₂'_term, jacobiTheta₂_term, ofReal_exp, mul_assoc (-I * n), ← Complex.exp_add,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:67:    (fun ξ : ℝ ↦ rexp (-π * ξ ^ 2 * x) * re (jacobiTheta₂ (ξ * I * x) (I * x))) 1 by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:69:      simp only [ofReal_add, ofReal_one, add_mul, one_mul, jacobiTheta₂_add_left']
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:78:    ↑(evenKernel ↑a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x) := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:79:  simp [evenKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:85:  | H a' => simp [← ofReal_inj, evenKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im ≤ 0)]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:90:  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂ ξ (I * x))) 1 by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:91:    intro ξ; simp [jacobiTheta₂_add_left]).lift a
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:93:lemma cosKernel_def (a x : ℝ) : ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x) := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:94:  simp [cosKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:99:  | H => simp [← ofReal_inj, cosKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im ≤ 0)]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:109:  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, evenKernel_def, jacobiTheta₂_neg_left]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:121:  exact (continuousAt_jacobiTheta₂ (a' * I * x) <| by simpa).comp
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:129:  exact (continuousAt_jacobiTheta₂ a' <| by simpa).comp
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:138:  rw [← ofReal_inj, ofReal_mul, evenKernel_def, cosKernel_def, jacobiTheta₂_functional_equation]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:167:      jacobiTheta₂_term n (a * I * t) (I * t) := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:168:    rw [jacobiTheta₂_term, ← Complex.exp_add]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:170:  simpa [this] using (hasSum_jacobiTheta₂_term _ (by simpa)).mul_left _
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:176:      jacobiTheta₂_term n a (I * ↑t) := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:177:    rw [jacobiTheta₂_term, ← Complex.exp_add]
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:180:  simpa [this] using hasSum_jacobiTheta₂_term _ (by simpa)
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:18:`jacobiSum χ ψ = ∑ x : R, χ x * ψ (1 - x)`
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:20:(see `jacobiSum`) and provides some basic results and API lemmas on Jacobi sums.
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:43:-- need `Fintype` instead of `Finite` to make `jacobiSum` computable.
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:47:def jacobiSum (χ ψ : MulChar R R') : R' :=
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:50:lemma jacobiSum_comm (χ ψ : MulChar R R') : jacobiSum χ ψ = jacobiSum ψ χ := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:51:  simp only [jacobiSum, mul_comm (χ _)]
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:56:lemma jacobiSum_ringHomComp {R'' : Type*} [CommRing R''] (χ ψ : MulChar R R') (f : R' →+* R'') :
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:57:    jacobiSum (χ.ringHomComp f) (ψ.ringHomComp f) = f (jacobiSum χ ψ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:58:  simp only [jacobiSum, MulChar.ringHomComp, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:73:lemma jacobiSum_eq_sum_sdiff (χ ψ : MulChar F R) :
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:74:    jacobiSum χ ψ = ∑ x ∈ univ \ {0,1}, χ x * ψ (1 - x) := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:75:  simp only [jacobiSum, subset_univ, sum_sdiff_eq_sub, sub_eq_add_neg, left_eq_add,
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:81:private lemma jacobiSum_eq_aux (χ ψ : MulChar F R) :
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:82:    jacobiSum χ ψ = ∑ x : F, χ x + ∑ x : F, ψ x - Fintype.card F +
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:84:  rw [jacobiSum]
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:103:theorem jacobiSum_trivial_trivial :
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:104:    jacobiSum (MulChar.trivial F R) (MulChar.trivial F R) = Fintype.card F - 2 := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:106:  rw [jacobiSum_eq_sum_sdiff]
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:120:theorem jacobiSum_one_one : jacobiSum (1 : MulChar F R) 1 = Fintype.card F - 2 :=
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:121:  jacobiSum_trivial_trivial
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:126:theorem jacobiSum_one_nontrivial {χ : MulChar F R} (hχ : χ ≠ 1) : jacobiSum 1 χ = -1 := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:133:  simp only [jacobiSum_eq_aux, MulChar.sum_one_eq_card_units, MulChar.sum_eq_zero_of_ne_one hχ,
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:139:theorem jacobiSum_nontrivial_inv {χ : MulChar F R} (hχ : χ ≠ 1) : jacobiSum χ χ⁻¹ = -χ (-1) := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:141:  rw [jacobiSum]
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:165:theorem jacobiSum_mul_nontrivial {χ φ : MulChar F R} (h : χ * φ ≠ 1) (ψ : AddChar F R) :
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:166:    gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:182:  rw [← jacobiSum, ← sum_mul, gaussSum, sum_eq_sum_diff_singleton_add (mem_univ (0 : F)),
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:193:theorem jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum (h : (Fintype.card F : F') ≠ 0)
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:195:    jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ / gaussSum (χ * φ) ψ := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:197:  exact jacobiSum_mul_nontrivial hχφ ψ
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:203:lemma jacobiSum_mul_jacobiSum_inv (h : ringChar F' ≠ ringChar F) {χ φ : MulChar F F'} (hχ : χ ≠ 1)
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:205:    jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = Fintype.card F := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:216:  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp]
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:232:  rw [mul_mul_mul_comm, jacobiSum_mul_nontrivial Hχφ, mul_inv, ← ringHomComp_inv,
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:233:    ← ringHomComp_inv, jacobiSum_mul_nontrivial Hχφ', map_natCast, ← mul_mul_mul_comm,
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:278:lemma jacobiSum_mem_algebraAdjoin_of_pow_eq_one {n : ℕ} [NeZero n] {χ φ : MulChar F R}
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:280:    jacobiSum χ φ ∈ ℤ[μ] :=
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:289:lemma exists_jacobiSum_eq_neg_one_add {n : ℕ} (hn : 2 < n) {χ ψ : MulChar F R}
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:292:    ∃ z ∈ ℤ[μ], jacobiSum χ ψ = -1 + z * (μ - 1) ^ 2 := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:297:  · rw [hχ₀, hψ₀, jacobiSum_one_one]
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:302:    rw [hχ₀, jacobiSum_one_nontrivial hψ₀, zero_mul, add_zero]
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:304:    rw [jacobiSum_comm, hψ₀, jacobiSum_one_nontrivial hχ₀, zero_mul, add_zero]
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:306:    rw [jacobiSum_eq_aux, MulChar.sum_eq_zero_of_ne_one hχ₀, MulChar.sum_eq_zero_of_ne_one hψ₀, hq]
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:324:lemma gaussSum_pow_eq_prod_jacobiSum_aux (χ : MulChar F R) (ψ : AddChar F R) {n : ℕ}
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:326:    gaussSum χ ψ ^ n = gaussSum (χ ^ n) ψ * ∏ j ∈ Ico 1 n, jacobiSum χ (χ ^ j) := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:332:            jacobiSum χ (χ ^ n) * gaussSum (χ ^ (n + 1)) ψ := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:335:        rw [mul_comm, ← jacobiSum_mul_nontrivial hχn, mul_comm, ← pow_succ']
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:342:theorem gaussSum_pow_eq_prod_jacobiSum {χ : MulChar F R} {ψ : AddChar F R} (hχ : 2 ≤ orderOf χ)
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:345:      χ (-1) * Fintype.card F * ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χ (χ ^ i) := by
.lake/packages/mathlib/Mathlib/NumberTheory/JacobiSum/Basic.lean:346:  have := gaussSum_pow_eq_prod_jacobiSum_aux χ ψ (n := orderOf χ - 1) (by lia) (by lia)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/Bounds.lean:89:    refine (((summable_pow_mul_jacobiTheta₂_term_bound (|a| * t) ht k).mul_right
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/Manifold.lean:28:theorem mdifferentiable_jacobiTheta : MDiff (jacobiTheta ∘ (↑) : ℍ → ℂ) :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/Manifold.lean:29:  fun τ => (differentiableAt_jacobiTheta τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:29:noncomputable def jacobiTheta (τ : ℂ) : ℂ := ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * τ)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:31:lemma jacobiTheta_eq_jacobiTheta₂ (τ : ℂ) : jacobiTheta τ = jacobiTheta₂ 0 τ :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:32:  tsum_congr (by simp [jacobiTheta₂_term])
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:34:theorem jacobiTheta_two_add (τ : ℂ) : jacobiTheta (2 + τ) = jacobiTheta τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:35:  simp_rw [jacobiTheta_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_right]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:37:theorem jacobiTheta_T_sq_smul (τ : ℍ) : jacobiTheta (ModularGroup.T ^ 2 • τ :) = jacobiTheta τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:38:  suffices (ModularGroup.T ^ 2 • τ :) = (2 : ℂ) + ↑τ by simp_rw [this, jacobiTheta_two_add]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:43:theorem jacobiTheta_S_smul (τ : ℍ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:44:    jacobiTheta ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:49:  simp_rw [UpperHalfPlane.modular_S_smul, jacobiTheta_eq_jacobiTheta₂, ← ofReal_zero]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:51:  simp_rw [jacobiTheta₂_functional_equation 0 τ, zero_pow two_ne_zero, mul_zero, zero_div,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:71:theorem hasSum_nat_jacobiTheta {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:72:    HasSum (fun n : ℕ => cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)) ((jacobiTheta τ - 1) / 2) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:73:  have := hasSum_jacobiTheta₂_term 0 hτ
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:74:  simp_rw [jacobiTheta₂_term, mul_zero, zero_add, ← jacobiTheta_eq_jacobiTheta₂] at this
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:84:theorem jacobiTheta_eq_tsum_nat {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:85:    jacobiTheta τ = ↑1 + ↑2 * ∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:86:  rw [(hasSum_nat_jacobiTheta hτ).tsum_eq, mul_div_cancel₀ _ (two_ne_zero' ℂ), ← add_sub_assoc,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:89:/-- An explicit upper bound for `‖jacobiTheta τ - 1‖`. -/
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:90:theorem norm_jacobiTheta_sub_one_le {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:91:    ‖jacobiTheta τ - 1‖ ≤ 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:95:      ‖jacobiTheta τ - 1‖ = ↑2 * ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)‖ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:96:        rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat hτ), norm_mul, Complex.norm_two]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:111:/-- The norm of `jacobiTheta τ - 1` decays exponentially as `im τ → ∞`. -/
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:112:theorem isBigO_at_im_infty_jacobiTheta_sub_one :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:113:    (fun τ => jacobiTheta τ - 1) =O[comap im atTop] fun τ => rexp (-π * τ.im) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:116:    (norm_jacobiTheta_sub_one_le (hτ.symm ▸ zero_lt_one.trans_le hy : 0 < im τ)).trans ?_⟩
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:121:theorem differentiableAt_jacobiTheta {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:122:    DifferentiableAt ℂ jacobiTheta τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:123:  simp_rw [funext jacobiTheta_eq_jacobiTheta₂]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:124:  exact differentiableAt_jacobiTheta₂_snd 0 hτ
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:126:theorem continuousAt_jacobiTheta {τ : ℂ} (hτ : 0 < im τ) : ContinuousAt jacobiTheta τ :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:127:  (differentiableAt_jacobiTheta hτ).continuousAt
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:45:def jacobiTheta₂_term (n : ℤ) (z τ : ℂ) : ℂ := cexp (2 * π * I * n * z + π * I * n ^ 2 * τ)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:48:def jacobiTheta₂_term_fderiv (n : ℤ) (z τ : ℂ) : ℂ × ℂ →L[ℂ] ℂ :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:53:lemma hasFDerivAt_jacobiTheta₂_term (n : ℤ) (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:54:    HasFDerivAt (fun p : ℂ × ℂ ↦ jacobiTheta₂_term n p.1 p.2)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:55:    (jacobiTheta₂_term_fderiv n z τ) (z, τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:62:def jacobiTheta₂'_term (n : ℤ) (z τ : ℂ) := 2 * π * I * n * jacobiTheta₂_term n z τ
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:70:We show that the sums of the three functions `jacobiTheta₂_term`, `jacobiTheta₂'_term` and
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:71:`jacobiTheta₂_term_fderiv` are locally uniformly convergent in the domain `0 < im τ`, and diverge
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:75:lemma norm_jacobiTheta₂_term (n : ℤ) (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:76:    ‖jacobiTheta₂_term n z τ‖ = rexp (-π * n ^ 2 * τ.im - 2 * π * n * z.im) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:77:  rw [jacobiTheta₂_term, Complex.norm_exp, (by push_cast; ring :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:82:/-- A uniform upper bound for `jacobiTheta₂_term` on compact subsets. -/
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:83:lemma norm_jacobiTheta₂_term_le {S T : ℝ} (hT : 0 < T) {z τ : ℂ}
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:85:    ‖jacobiTheta₂_term n z τ‖ ≤ rexp (-π * (T * n ^ 2 - 2 * S * |n|)) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:86:  simp_rw [norm_jacobiTheta₂_term, Real.exp_le_exp, sub_eq_add_neg, neg_mul, ← neg_add,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:95:/-- A uniform upper bound for `jacobiTheta₂'_term` on compact subsets. -/
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:96:lemma norm_jacobiTheta₂'_term_le {S T : ℝ} (hT : 0 < T) {z τ : ℂ}
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:98:    ‖jacobiTheta₂'_term n z τ‖ ≤ 2 * π * |n| * rexp (-π * (T * n ^ 2 - 2 * S * |n|)) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:99:  rw [jacobiTheta₂'_term, norm_mul]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:100:  refine mul_le_mul (le_of_eq ?_) (norm_jacobiTheta₂_term_le hT hz hτ n)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:107:lemma summable_pow_mul_jacobiTheta₂_term_bound (S : ℝ) {T : ℝ} (hT : 0 < T) (k : ℕ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:123:lemma summable_jacobiTheta₂_term_iff (z τ : ℂ) : Summable (jacobiTheta₂_term · z τ) ↔ 0 < im τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:127:  · refine (summable_pow_mul_jacobiTheta₂_term_bound |im z| hτ 0).of_norm_bounded ?_
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:128:    simpa only [pow_zero, one_mul] using norm_jacobiTheta₂_term_le hτ le_rfl le_rfl
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:132:      suffices Tendsto (fun n : ℕ ↦ ‖jacobiTheta₂_term ↑n z τ‖) atTop atTop by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:135:      simp only [norm_jacobiTheta₂_term, Int.cast_natCast]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:144:      simp_rw [← summable_norm_iff (E := ℂ), norm_jacobiTheta₂_term, hτ, mul_zero, zero_sub] at h
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:162:lemma norm_jacobiTheta₂_term_fderiv_le (n : ℤ) (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:163:    ‖jacobiTheta₂_term_fderiv n z τ‖ ≤ 3 * π * |n| ^ 2 * ‖jacobiTheta₂_term n z τ‖ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:166:  rw [jacobiTheta₂_term_fderiv, jacobiTheta₂_term, hns,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:179:lemma norm_jacobiTheta₂_term_fderiv_ge (n : ℤ) (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:180:    π * |n| ^ 2 * ‖jacobiTheta₂_term n z τ‖ ≤ ‖jacobiTheta₂_term_fderiv n z τ‖ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:181:  have : ‖(jacobiTheta₂_term_fderiv n z τ) (0, 1)‖ ≤ ‖jacobiTheta₂_term_fderiv n z τ‖ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:185:  simp_rw [jacobiTheta₂_term_fderiv, jacobiTheta₂_term, ContinuousLinearMap.coe_smul',
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:193:lemma summable_jacobiTheta₂_term_fderiv_iff (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:194:    Summable (jacobiTheta₂_term_fderiv · z τ) ↔ 0 < im τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:196:  · rw [← summable_jacobiTheta₂_term_iff (z := z)]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:203:    refine le_trans ?_ (norm_jacobiTheta₂_term_fderiv_ge n z τ)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:210:    refine ((summable_pow_mul_jacobiTheta₂_term_bound
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:212:    refine (norm_jacobiTheta₂_term_fderiv_le n z τ).trans
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:213:      (?_ : 3 * π * |n| ^ 2 * ‖jacobiTheta₂_term n z τ‖ ≤ _)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:217:    exact norm_jacobiTheta₂_term_le hτ le_rfl le_rfl n
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:219:lemma summable_jacobiTheta₂'_term_iff (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:220:    Summable (jacobiTheta₂'_term · z τ) ↔ 0 < im τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:222:  · rw [← summable_jacobiTheta₂_term_iff (z := z)]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:227:    rw [jacobiTheta₂'_term, norm_mul, ← mul_assoc]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:235:  · refine fun hτ ↦ ((summable_pow_mul_jacobiTheta₂_term_bound
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:237:    rw [jacobiTheta₂'_term, norm_mul, ← mul_assoc, pow_one]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:238:    refine mul_le_mul (le_of_eq ?_) (norm_jacobiTheta₂_term_le hτ le_rfl le_rfl n)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:252:def jacobiTheta₂ (z τ : ℂ) : ℂ := ∑' n : ℤ, jacobiTheta₂_term n z τ
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:255:def jacobiTheta₂_fderiv (z τ : ℂ) : ℂ × ℂ →L[ℂ] ℂ := ∑' n : ℤ, jacobiTheta₂_term_fderiv n z τ
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:260:def jacobiTheta₂' (z τ : ℂ) := ∑' n : ℤ, jacobiTheta₂'_term n z τ
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:262:lemma hasSum_jacobiTheta₂_term (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:263:    HasSum (fun n ↦ jacobiTheta₂_term n z τ) (jacobiTheta₂ z τ) :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:264:  ((summable_jacobiTheta₂_term_iff z τ).mpr hτ).hasSum
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:266:lemma hasSum_jacobiTheta₂_term_fderiv (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:267:    HasSum (fun n ↦ jacobiTheta₂_term_fderiv n z τ) (jacobiTheta₂_fderiv z τ) :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:268:  ((summable_jacobiTheta₂_term_fderiv_iff z τ).mpr hτ).hasSum
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:270:lemma hasSum_jacobiTheta₂'_term (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:271:    HasSum (fun n ↦ jacobiTheta₂'_term n z τ) (jacobiTheta₂' z τ) :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:272:  ((summable_jacobiTheta₂'_term_iff z τ).mpr hτ).hasSum
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:274:lemma jacobiTheta₂_undef (z : ℂ) {τ : ℂ} (hτ : im τ ≤ 0) : jacobiTheta₂ z τ = 0 := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:276:  rw [summable_jacobiTheta₂_term_iff]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:279:lemma jacobiTheta₂_fderiv_undef (z : ℂ) {τ : ℂ} (hτ : im τ ≤ 0) : jacobiTheta₂_fderiv z τ = 0 := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:281:  rw [summable_jacobiTheta₂_term_fderiv_iff]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:284:lemma jacobiTheta₂'_undef (z : ℂ) {τ : ℂ} (hτ : im τ ≤ 0) : jacobiTheta₂' z τ = 0 := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:286:  rw [summable_jacobiTheta₂'_term_iff]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:293:lemma hasFDerivAt_jacobiTheta₂ (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:294:    HasFDerivAt (fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2) (jacobiTheta₂_fderiv z τ) (z, τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:305:  let f : ℤ → ℂ × ℂ → ℂ := fun n p ↦ jacobiTheta₂_term n p.1 p.2
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:306:  let f' : ℤ → ℂ × ℂ → ℂ × ℂ →L[ℂ] ℂ := fun n p ↦ jacobiTheta₂_term_fderiv n p.1 p.2
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:308:    fun p _ ↦ hasFDerivAt_jacobiTheta₂_term n p.1 p.2
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:311:    refine fun n p hp ↦ (norm_jacobiTheta₂_term_fderiv_le n p.1 p.2).trans ?_
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:313:    exact norm_jacobiTheta₂_term_le hT (le_of_lt hp.1) (le_of_lt hp.2) n
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:316:    exact (summable_pow_mul_jacobiTheta₂_term_bound S hT 2).mul_left _
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:318:    refine (summable_pow_mul_jacobiTheta₂_term_bound S hT 0).of_norm_bounded ?_
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:319:    simpa only [pow_zero, one_mul] using norm_jacobiTheta₂_term_le hT hz.le hτ'.le
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:320:  simpa only [jacobiTheta₂, jacobiTheta₂_fderiv, f, f'] using
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:323:lemma continuousAt_jacobiTheta₂ (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:324:    ContinuousAt (fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2) (z, τ) :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:325:  (hasFDerivAt_jacobiTheta₂ z hτ).continuousAt
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:328:lemma differentiableAt_jacobiTheta₂_fst (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:329:    DifferentiableAt ℂ (jacobiTheta₂ · τ) z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:330:  ((hasFDerivAt_jacobiTheta₂ z hτ).comp (𝕜 := ℂ) z (hasFDerivAt_prodMk_left z τ) :).differentiableAt
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:333:lemma differentiableAt_jacobiTheta₂_snd (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:334:    DifferentiableAt ℂ (jacobiTheta₂ z) τ :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:335:  ((hasFDerivAt_jacobiTheta₂ z hτ).comp τ (hasFDerivAt_prodMk_right z τ)).differentiableAt
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:337:lemma hasDerivAt_jacobiTheta₂_fst (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:338:    HasDerivAt (jacobiTheta₂ · τ) (jacobiTheta₂' z τ) z := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:346:  have step1 : HasSum (fun n ↦ (jacobiTheta₂_term_fderiv n z τ) (1, 0))
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:347:      ((jacobiTheta₂_fderiv z τ) (1, 0)) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:348:    apply eval_fst_CLM.hasSum (hasSum_jacobiTheta₂_term_fderiv z hτ)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:349:  have step2 (n : ℤ) : (jacobiTheta₂_term_fderiv n z τ) (1, 0) = jacobiTheta₂'_term n z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:350:    simp only [jacobiTheta₂_term_fderiv, smul_add, ContinuousLinearMap.add_apply,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:352:      mul_one, ContinuousLinearMap.coe_snd', mul_zero, add_zero, jacobiTheta₂'_term,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:353:      jacobiTheta₂_term, mul_comm _ (cexp _)]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:355:  have step3 : HasDerivAt (fun x ↦ jacobiTheta₂ x τ) ((jacobiTheta₂_fderiv z τ) (1, 0)) z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:356:    (((hasFDerivAt_jacobiTheta₂ z hτ).comp z (hasFDerivAt_prodMk_left z τ)).hasDerivAt :)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:359:lemma continuousAt_jacobiTheta₂' (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:360:    ContinuousAt (fun p : ℂ × ℂ ↦ jacobiTheta₂' p.1 p.2) (z, τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:369:      using (summable_pow_mul_jacobiTheta₂_term_bound S hT 1).mul_left (2 * π)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:372:    unfold jacobiTheta₂'_term jacobiTheta₂_term
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:374:  · exact norm_jacobiTheta₂'_term_le hT (le_of_lt hz') (le_of_lt hτ') n
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:381:lemma jacobiTheta₂_add_right (z τ : ℂ) : jacobiTheta₂ z (τ + 2) = jacobiTheta₂ z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:383:  simp_rw [jacobiTheta₂_term, Complex.exp_add]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:389:lemma jacobiTheta₂_add_left (z τ : ℂ) : jacobiTheta₂ (z + 1) τ = jacobiTheta₂ z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:391:  simp_rw [jacobiTheta₂_term, mul_add, Complex.exp_add, mul_one, mul_comm _ (n : ℂ),
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:395:lemma jacobiTheta₂_add_left' (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:396:    jacobiTheta₂ (z + τ) τ = cexp (-π * I * (τ + 2 * z)) * jacobiTheta₂ z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:397:  conv_rhs => rw [jacobiTheta₂, ← tsum_mul_left, ← (Equiv.addRight 1).tsum_eq]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:399:  simp_rw [jacobiTheta₂_term, ← Complex.exp_add, Equiv.coe_addRight, Int.cast_add]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:404:lemma jacobiTheta₂_neg_left (z τ : ℂ) : jacobiTheta₂ (-z) τ = jacobiTheta₂ z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:405:  conv_lhs => rw [jacobiTheta₂, ← Equiv.tsum_eq (Equiv.neg ℤ)]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:407:  simp_rw [jacobiTheta₂_term, Equiv.neg_apply, Int.cast_neg, neg_sq, mul_assoc, neg_mul_neg]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:409:lemma jacobiTheta₂_conj (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:410:    conj (jacobiTheta₂ z τ) = jacobiTheta₂ (conj z) (-conj τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:411:  rw [← jacobiTheta₂_neg_left, jacobiTheta₂, conj_tsum]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:413:  simp only [jacobiTheta₂_term, mul_neg, ← exp_conj, map_add, map_neg, map_mul, map_ofNat,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:416:lemma jacobiTheta₂'_add_right (z τ : ℂ) : jacobiTheta₂' z (τ + 2) = jacobiTheta₂' z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:418:  simp_rw [jacobiTheta₂'_term, jacobiTheta₂_term, Complex.exp_add]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:423:lemma jacobiTheta₂'_add_left (z τ : ℂ) : jacobiTheta₂' (z + 1) τ = jacobiTheta₂' z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:424:  unfold jacobiTheta₂' jacobiTheta₂'_term jacobiTheta₂_term
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:429:lemma jacobiTheta₂'_add_left' (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:430:    jacobiTheta₂' (z + τ) τ =
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:431:      cexp (-π * I * (τ + 2 * z)) * (jacobiTheta₂' z τ - 2 * π * I * jacobiTheta₂ z τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:433:  · simp_rw [jacobiTheta₂_undef _ hτ, jacobiTheta₂'_undef _ hτ, mul_zero, sub_zero, mul_zero]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:434:  have (n : ℤ) : jacobiTheta₂'_term n (z + τ) τ =
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:435:      cexp (-π * I * (τ + 2 * z)) * (jacobiTheta₂'_term (n + 1) z τ -
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:436:      2 * π * I * jacobiTheta₂_term (n + 1) z τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:437:    simp only [jacobiTheta₂'_term, jacobiTheta₂_term]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:442:  rw [jacobiTheta₂', funext this, tsum_mul_left, ← (Equiv.subRight (1 : ℤ)).tsum_eq]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:443:  simp only [jacobiTheta₂, jacobiTheta₂', Equiv.subRight_apply, sub_add_cancel,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:444:    (hasSum_jacobiTheta₂'_term z hτ).summable.tsum_sub
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:445:    ((hasSum_jacobiTheta₂_term z hτ).summable.mul_left _), tsum_mul_left]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:447:lemma jacobiTheta₂'_neg_left (z τ : ℂ) : jacobiTheta₂' (-z) τ = -jacobiTheta₂' z τ := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:448:  rw [jacobiTheta₂', jacobiTheta₂', ← tsum_neg, ← (Equiv.neg ℤ).tsum_eq]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:450:  simp only [jacobiTheta₂'_term, jacobiTheta₂_term]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:455:lemma jacobiTheta₂'_conj (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:456:    conj (jacobiTheta₂' z τ) = jacobiTheta₂' (conj z) (-conj τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:457:  rw [← neg_inj, ← jacobiTheta₂'_neg_left, jacobiTheta₂', jacobiTheta₂', conj_tsum, ← tsum_neg]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:459:  simp_rw [jacobiTheta₂'_term, jacobiTheta₂_term, map_mul, ← Complex.exp_conj, map_add, map_mul,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:467:/-- The functional equation for the Jacobi theta function: `jacobiTheta₂ z τ` is an explicit factor
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:468:times `jacobiTheta₂ (z / τ) (-1 / τ)`. This is the key lemma behind the proof of the functional
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:470:theorem jacobiTheta₂_functional_equation (z τ : ℂ) : jacobiTheta₂ z τ =
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:471:    1 / (-I * τ) ^ (1 / 2 : ℂ) * cexp (-π * I * z ^ 2 / τ) * jacobiTheta₂ (z / τ) (-1 / τ) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:476:    rw [jacobiTheta₂_undef z hτ, jacobiTheta₂_undef _ this, mul_zero]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:477:  unfold jacobiTheta₂ jacobiTheta₂_term
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:498:`jacobiTheta₂' z τ` to `jacobiTheta₂' (z / τ) (-1 / τ)`. This is the key lemma behind the proof of
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:500:theorem jacobiTheta₂'_functional_equation (z τ : ℂ) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:501:    jacobiTheta₂' z τ = 1 / (-I * τ) ^ (1 / 2 : ℂ) * cexp (-π * I * z ^ 2 / τ) / τ *
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:502:      (jacobiTheta₂' (z / τ) (-1 / τ) - 2 * π * I * z * jacobiTheta₂ (z / τ) (-1 / τ)) := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:504:  · rw [jacobiTheta₂'_undef z hτ, jacobiTheta₂'_undef, jacobiTheta₂_undef, mul_zero,
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:511:  have hj : HasDerivAt (fun w ↦ jacobiTheta₂ (w / τ) (-1 / τ))
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:512:      ((1 / τ) * jacobiTheta₂' (z / τ) (-1 / τ)) z := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:513:    have := hasDerivAt_jacobiTheta₂_fst (z / τ) hτ'
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:516:  _ = deriv (jacobiTheta₂ · τ) z := (hasDerivAt_jacobiTheta₂_fst z hτ).deriv.symm
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:518:        cexp (-π * I * z ^ 2 / τ) * jacobiTheta₂ (z / τ) (-1 / τ)) z := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:519:    rw [funext (jacobiTheta₂_functional_equation · τ)]
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:521:        deriv (fun z ↦ cexp (-π * I * z ^ 2 / τ) * jacobiTheta₂ (z / τ) (-1 / τ)) z := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:524:        (deriv (fun z ↦ cexp (-π * I * z ^ 2 / τ)) z * jacobiTheta₂ (z / τ) (-1 / τ)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:525:         + cexp (-π * I * z ^ 2 / τ) * deriv (fun z ↦ jacobiTheta₂ (z / τ) (-1 / τ)) z) := by
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:286:lemma universalFactorizationMapPresentation_jacobiMatrix :
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:288:    (universalFactorizationMapPresentation R n m k hn).jacobiMatrix =
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:297:  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:303:lemma universalFactorizationMapPresentation_jacobian :
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:305:    (universalFactorizationMapPresentation R n m k hn).jacobian =
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:312:  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:313:    MvPolynomial.universalFactorizationMapPresentation_jacobiMatrix]
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:504:Its jacobian is the resultant of the two factors (up to sign). -/
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:511:lemma UniversalFactorizationRing.jacobian_resentation :
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:512:    (presentation m k hn p).jacobian =
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:522:  refine (Algebra.PreSubmersivePresentation.baseChange_jacobian _ _).trans ?_
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:524:  rw [MvPolynomial.universalFactorizationMapPresentation_jacobian]
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:537:  Localization.Away (M := 𝓡) (presentation m k hn p).jacobian
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:563:  rw [← map_mul, ← UniversalFactorizationRing.jacobian_resentation m k hn p]
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:568:  let Δ : 𝓡 := (presentation m k hn p).jacobian
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:574:      jacobian_isUnit := by simpa [Algebra.smul_def, -isUnit_map_iff, hΔ] }
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:596:      (M := .powers (UniversalFactorizationRing.presentation m k hn p).jacobian) ?_
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:601:    rw [← AlgHom.coe_toRingHom, UniversalFactorizationRing.jacobian_resentation, map_mul,
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean:613:      (.powers (UniversalFactorizationRing.presentation m k hn p).jacobian)
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/StandardSmooth.lean:237:    jacobian_isUnit := by
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/StandardSmooth.lean:238:      convert P.jacobian_isUnit using 1
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/StandardSmooth.lean:239:      simp_rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, map_det]
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/StandardSmooth.lean:243:      · simpa [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, P',
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/StandardSmooth.lean:246:        simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, this]
.lake/packages/mathlib/Mathlib/RingTheory/Smooth/StandardSmoothOfFree.lean:76:    ⟨P', P'.isUnit_jacobian_of_cotangentRestrict_bijective bcot hbcot hbij⟩
.lake/packages/mathlib/Mathlib/RingTheory/Smooth/Fiber.lean:110:  The key is then to use jacobi criterion `FormallySmooth.iff_injective_cotangentComplexBaseChange`.
.lake/packages/mathlib/Mathlib/RingTheory/Etale/StandardEtale.lean:311:attribute [local simp] Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det
.lake/packages/mathlib/Mathlib/RingTheory/Etale/StandardEtale.lean:312:  Matrix.det_fin_two Algebra.PreSubmersivePresentation.jacobiMatrix_apply
.lake/packages/mathlib/Mathlib/RingTheory/Etale/StandardEtale.lean:323:  jacobian_isUnit := by simp [P.hasMap.2, P.hasMap.isUnit_derivative_f]
.lake/packages/mathlib/Mathlib/RingTheory/Etale/StandardEtale.lean:325:lemma StandardEtalePresentation.toSubmersivePresentation_jacobian :
.lake/packages/mathlib/Mathlib/RingTheory/Etale/StandardEtale.lean:326:    P.toSubmersivePresentation.jacobian = aeval P.x P.f.derivative * aeval P.x P.g := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/CrossProduct.lean:29:* `jacobi_cross`
.lake/packages/mathlib/Mathlib/LinearAlgebra/CrossProduct.lean:145:theorem jacobi_cross (u v w : Fin 3 → R) : u ⨯₃ (v ⨯₃ w) + v ⨯₃ (w ⨯₃ u) + w ⨯₃ (u ⨯₃ v) = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/CrossProduct.lean:146:  lie_jacobi u v w
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:29:  the following steps; see `NormNum.jacobiSymNat`. (But we'll continue to write `J(a | b)`
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:58:def jacobiSymNat (a b : ℕ) : ℤ :=
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:59:  jacobiSym a b
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:64:We repeat part of the API for `jacobiSym` with `NormNum.jacobiSymNat` and without implicit
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:70:theorem jacobiSymNat.zero_right (a : ℕ) : jacobiSymNat a 0 = 1 := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:71:  rw [jacobiSymNat, jacobiSym.zero_right]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:73:theorem jacobiSymNat.one_right (a : ℕ) : jacobiSymNat a 1 = 1 := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:74:  rw [jacobiSymNat, jacobiSym.one_right]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:76:theorem jacobiSymNat.zero_left (b : ℕ) (hb : Nat.beq (b / 2) 0 = false) : jacobiSymNat 0 b = 0 := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:77:  rw [jacobiSymNat, Nat.cast_zero, jacobiSym.zero_left ?_]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:84:theorem jacobiSymNat.one_left (b : ℕ) : jacobiSymNat 1 b = 1 := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:85:  rw [jacobiSymNat, Nat.cast_one, jacobiSym.one_left]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:88:theorem LegendreSym.to_jacobiSym (p : ℕ) (pp : Fact p.Prime) (a r : ℤ)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:89:    (hr : IsInt (jacobiSym a p) r) : IsInt (legendreSym p a) r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:90:  rwa [@jacobiSym.legendreSym.to_jacobiSym p pp a]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:94:    (hab : a % b' = ab) (h : (ab' : ℤ) = ab) (hr : jacobiSymNat ab' b = r) : jacobiSym a b = r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:95:  rw [← hr, jacobiSymNat, jacobiSym.mod_left, hb', hab, ← h]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:97:theorem jacobiSymNat.mod_left (a b ab : ℕ) (r : ℤ) (hab : a % b = ab) (hr : jacobiSymNat ab b = r) :
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:98:    jacobiSymNat a b = r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:99:  rw [← hr, jacobiSymNat, jacobiSymNat, _root_.jacobiSym.mod_left a b, ← hab]; rfl
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:102:theorem jacobiSymNat.even_even (a b : ℕ) (hb₀ : Nat.beq (b / 2) 0 = false) (ha : a % 2 = 0)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:103:    (hb₁ : b % 2 = 0) : jacobiSymNat a b = 0 := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:104:  refine jacobiSym.eq_zero_iff.mpr
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:113:theorem jacobiSymNat.odd_even (a b c : ℕ) (r : ℤ) (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : b / 2 = c)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:114:    (hr : jacobiSymNat a c = r) : jacobiSymNat a b = r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:121:    -- for `jacobiSym.mul_right`
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:122:    rwa [← Nat.mod_add_div b 2, hb, hc, Nat.zero_add, jacobiSymNat, jacobiSym.mul_right,
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:123:      ← jacobiSym.legendreSym.to_jacobiSym, ha', one_mul]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:126:theorem jacobiSymNat.double_even (a b c : ℕ) (r : ℤ) (ha : a % 4 = 0) (hb : b % 2 = 1)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:127:    (hc : a / 4 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:128:  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:129:  exact (jacobiSym.div_four_left (mod_cast ha) hb).symm
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:134:theorem jacobiSymNat.even_odd₁ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 1)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:135:    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:136:  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:137:  rw [← jacobiSym.even_odd (mod_cast ha), if_neg (by simp [hb])]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:140:theorem jacobiSymNat.even_odd₇ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 7)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:141:    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:142:  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:143:  rw [← jacobiSym.even_odd (mod_cast ha), if_neg (by simp [hb])]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:146:theorem jacobiSymNat.even_odd₃ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 3)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:147:    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = -r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:148:  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:149:  rw [← jacobiSym.even_odd (mod_cast ha), if_pos (by simp [hb])]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:152:theorem jacobiSymNat.even_odd₅ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 5)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:153:    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = -r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:154:  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:155:  rw [← jacobiSym.even_odd (mod_cast ha), if_pos (by simp [hb])]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:159:theorem jacobiSymNat.qr₁ (a b : ℕ) (r : ℤ) (ha : a % 4 = 1) (hb : b % 2 = 1)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:160:    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:161:  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_one_mod_four ha (Nat.odd_iff.mpr hb)]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:163:theorem jacobiSymNat.qr₁_mod (a b ab : ℕ) (r : ℤ) (ha : a % 4 = 1) (hb : b % 2 = 1)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:164:    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = r :=
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:165:  jacobiSymNat.qr₁ _ _ _ ha hb <| jacobiSymNat.mod_left _ _ ab r hab hr
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:167:theorem jacobiSymNat.qr₁' (a b : ℕ) (r : ℤ) (ha : a % 2 = 1) (hb : b % 4 = 1)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:168:    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:169:  rwa [jacobiSymNat, ← jacobiSym.quadratic_reciprocity_one_mod_four hb (Nat.odd_iff.mpr ha)]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:171:theorem jacobiSymNat.qr₁'_mod (a b ab : ℕ) (r : ℤ) (ha : a % 2 = 1) (hb : b % 4 = 1)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:172:    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = r :=
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:173:  jacobiSymNat.qr₁' _ _ _ ha hb <| jacobiSymNat.mod_left _ _ ab r hab hr
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:175:theorem jacobiSymNat.qr₃ (a b : ℕ) (r : ℤ) (ha : a % 4 = 3) (hb : b % 4 = 3)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:176:    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = -r := by
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:177:  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_three_mod_four ha hb, neg_inj]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:179:theorem jacobiSymNat.qr₃_mod (a b ab : ℕ) (r : ℤ) (ha : a % 4 = 3) (hb : b % 4 = 3)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:180:    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = -r :=
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:181:  jacobiSymNat.qr₃ _ _ _ ha hb <| jacobiSymNat.mod_left _ _ ab r hab hr
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:183:theorem isInt_jacobiSym : {a na : ℤ} → {b nb : ℕ} → {r : ℤ} →
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:184:    IsInt a na → IsNat b nb → jacobiSym na nb = r → IsInt (jacobiSym a b) r
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:187:theorem isInt_jacobiSymNat : {a na : ℕ} → {b nb : ℕ} → {r : ℤ} →
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:188:    IsNat a na → IsNat b nb → jacobiSymNat na nb = r → IsInt (jacobiSymNat a b) r
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:215:/-- This evaluates `r := jacobiSymNat a b` recursively using quadratic reciprocity
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:217:partial def proveJacobiSymOdd (ea eb : Q(ℕ)) : (er : Q(ℤ)) × Q(jacobiSymNat $ea $eb = $er) :=
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:221:    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:227:      ⟨mkRawIntLit' 0, q(jacobiSymNat.zero_left $eb $hb)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:230:      ⟨mkRawIntLit' 1, q(jacobiSymNat.one_left $eb)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:241:          ⟨er, q(jacobiSymNat.double_even $ea $eb $ec $er $ha $hb $hc $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:250:            ⟨er, q(jacobiSymNat.even_odd₁ $ea $eb $ec $er $ha $hb $hc $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:254:            show (_ : Q(ℤ)) × Q(jacobiSymNat $ea $eb = -$er) from
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:255:              ⟨er', q(jacobiSymNat.even_odd₃ $ea $eb $ec $er $ha $hb $hc $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:260:            ⟨er', q(jacobiSymNat.even_odd₅ $ea $eb $ec $er $ha $hb $hc $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:263:            ⟨er, q(jacobiSymNat.even_odd₇ $ea $eb $ec $er $ha $hb $hc $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:272:          ⟨er, q(jacobiSymNat.qr₁_mod $ea $eb $eab $er $ha $hb $hab $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:278:            ⟨er, q(jacobiSymNat.qr₁'_mod $ea $eb $eab $er $ha $hb $hab $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:284:            ⟨er', q(jacobiSymNat.qr₃_mod $ea $eb $eab $er $ha $hb $hab $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:286:/-- This evaluates `r := jacobiSymNat a b` and produces a proof term for the equality
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:288:partial def proveJacobiSymNat (ea eb : Q(ℕ)) : (er : Q(ℤ)) × Q(jacobiSymNat $ea $eb = $er) :=
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:292:    ⟨mkRawIntLit' 1, q(jacobiSymNat.zero_right $ea)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:295:    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:302:        show (er : Q(ℤ)) × Q(jacobiSymNat 0 $eb = $er) from
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:303:          ⟨mkRawIntLit' 0, q(jacobiSymNat.zero_left $eb $hb)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:305:        show (er : Q(ℤ)) × Q(jacobiSymNat 1 $eb = $er) from
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:306:          ⟨mkRawIntLit' 1, q(jacobiSymNat.one_left $eb)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:313:          ⟨mkRawIntLit' 0, q(jacobiSymNat.even_even $ea $eb $hb₀ $ha $hb₁)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:320:          ⟨er, q(jacobiSymNat.odd_even $ea $eb $ec $er $ha $hb $hc $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:327:        ⟨er, q(jacobiSymNat.mod_left $ea $eb $eab $er $hab $p)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:331:/-- This evaluates `r := jacobiSym a b` and produces a proof term for the equality.
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:332:This is done by reducing to `r := jacobiSymNat (a % b) b`. -/
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:333:partial def proveJacobiSym (ea : Q(ℤ)) (eb : Q(ℕ)) : (er : Q(ℤ)) × Q(jacobiSym $ea $eb = $er) :=
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:337:    ⟨mkRawIntLit' 1, q(jacobiSym.zero_right $ea)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:340:    ⟨mkRawIntLit' 1, q(jacobiSym.one_right $ea)⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:370:@[norm_num jacobiSym _ _]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:377:    haveI' : $e =Q jacobiSym $a $b := ⟨⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:378:    return .isInt _ er er.intLit! q(isInt_jacobiSym $pa $pb $pr)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:381:@[norm_num jacobiSymNat _ _]
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:388:    haveI' : $e =Q jacobiSymNat $a $b := ⟨⟩
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:389:    return .isInt _ er er.intLit!  q(isInt_jacobiSymNat $pa $pb $pr)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/LegendreSymbol.lean:402:      q(LegendreSym.to_jacobiSym $p $fp $a $er (isInt_jacobiSym $pa $pp $pr))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:111:theorem contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E => c) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:116:  contDiffAt_const.contDiffWithinAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:124:  rw [Subsingleton.elim f fun _ => 0]; exact contDiffAt_const
.lake/packages/mathlib/Mathlib/Order/BooleanAlgebra/Set.lean:166:lemma disjoint_compl_left_iff_subset : Disjoint sᶜ t ↔ t ⊆ s := disjoint_compl_left_iff
.lake/packages/mathlib/Mathlib/Order/BooleanAlgebra/Set.lean:171:alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_left⟩ := disjoint_compl_left_iff_subset
```

### Command

```sh
rg -n 'hasFDerivAt_det|hasDerivAt_det|deriv_det|fderiv_det|hasFDerivAt.*[Dd]et' .lake/packages/mathlib/Mathlib Poincare; rg -n 'det.*(deriv|Deriv)|[Dd]eriv.*det' Poincare/Global/VolumeDensity*
```

Exit: 1

```text
Poincare/Global/CoordinateVolumeDensityVariation.lean:67:theorem hasDerivAt_det_of_entries
Poincare/Global/CoordinateVolumeDensityVariation.lean:116:theorem hasDerivAt_det_eq_det_mul_trace
Poincare/Global/CoordinateVolumeDensityVariation.lean:122:  convert hasDerivAt_det_of_entries hA using 1
Poincare/Global/CoordinateVolumeDensityVariation.lean:161:  have hdet := hasDerivAt_det_eq_det_mul_trace hG hdetne
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-2.lean
```

Exit: 0

```text
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
```

### Command

```sh
cat Poincare/Global/CoordinateVolumeDensityVariation.lean
```

Exit: 0

```text
import Poincare.Global.VolumeDensity
import Poincare.Global.MetricRaiseTimeDerivative

/-!
# Coordinate volume-density variation

This file proves the finite-dimensional Jacobi formula directly from the
Leibniz expansion of the determinant and then differentiates
`sqrt |det G(t)|`.  The final section specializes the matrix path to the Gram
coefficients of a differentiable Riemannian metric path at a fixed point.

The results here are deliberately chart-local.  Passing from these coordinate
densities to the repo's Hausdorff-defined `volumeMeasure`, including chart
change, gluing, and differentiation under the integral, remains a separate
measure-theoretic bridge.
-/

noncomputable section

open Matrix

namespace Poincare

namespace VolumeDensity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first-order determinant variation, expressed by replacing one column
at a time by the corresponding column of the variation matrix. -/
def determinantColumnVariation (A B : Matrix ι ι ℝ) : ℝ :=
  ∑ i, (A.updateCol i (fun j => B j i)).det

private theorem prod_updateCol_eq
    (A B : Matrix ι ι ℝ) (σ : Equiv.Perm ι) (i : ι) :
    (∏ j, (A.updateCol i (fun k => B k i)) (σ j) j) =
      (∏ j ∈ Finset.univ.erase i, A (σ j) j) * B (σ i) i := by
  rw [← Finset.prod_erase_mul Finset.univ
    (fun j => (A.updateCol i (fun k => B k i)) (σ j) j)
    (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)
  · simp

/-- The replaced-column expression agrees with the derivative obtained by
differentiating the Leibniz formula term by term. -/
theorem determinantColumnVariation_eq_leibniz
    (A B : Matrix ι ι ℝ) :
    determinantColumnVariation A B =
      ∑ σ : Equiv.Perm ι,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * B (σ i) i := by
  classical
  rw [determinantColumnVariation]
  simp_rw [Matrix.det_apply']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _hσ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [prod_updateCol_eq]

/-- Entrywise differentiability of a square-matrix path differentiates its
determinant by the replaced-column formula. -/
theorem hasDerivAt_det_of_entries
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) t₀) :
    HasDerivAt (fun t => (A t).det)
      (determinantColumnVariation (A t₀) A') t₀ := by
  classical
  rw [determinantColumnVariation_eq_leibniz]
  rw [show (fun t => (A t).det) =
      fun t => ∑ σ : Equiv.Perm ι,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A t (σ i) i by
    funext t
    exact Matrix.det_apply' (A t)]
  apply HasDerivAt.fun_sum
  intro σ _hσ
  have hprod :
      HasDerivAt (fun t => ∏ i, A t (σ i) i)
        (∑ i, (∏ j ∈ Finset.univ.erase i, A t₀ (σ j) j) *
          A' (σ i) i) t₀ := by
    have hp :=
      HasDerivAt.finsetProd (u := Finset.univ)
        (f := fun i t => A t (σ i) i)
        (f' := fun i => A' (σ i) i)
        (fun i _hi => hA (σ i) i)
    exact hp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp)
  simpa using hprod.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ))

/-- Cramer's rule converts the replaced-column variation to contraction with
the adjugate matrix. -/
theorem determinantColumnVariation_eq_adjugate
    (A B : Matrix ι ι ℝ) :
    determinantColumnVariation A B =
      ∑ i, ∑ j, A.adjugate i j * B j i := by
  classical
  rw [determinantColumnVariation]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

/-- Over the reals, a non-singular adjugate is `det A` times the matrix
inverse, entrywise. -/
theorem det_mul_nonsing_inv_apply_eq_adjugate
    (A : Matrix ι ι ℝ) (hdet : A.det ≠ 0) (i j : ι) :
    A.det * A⁻¹ i j = A.adjugate i j := by
  rw [Matrix.inv_def]
  simp [hdet]

/-- Jacobi's formula for an entrywise differentiable real matrix path. -/
theorem hasDerivAt_det_eq_det_mul_trace
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) t₀)
    (hdet : (A t₀).det ≠ 0) :
    HasDerivAt (fun t => (A t).det)
      ((A t₀).det * ∑ i, ∑ j, (A t₀)⁻¹ i j * A' j i) t₀ := by
  convert hasDerivAt_det_of_entries hA using 1
  rw [determinantColumnVariation_eq_adjugate]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← mul_assoc, det_mul_nonsing_inv_apply_eq_adjugate (A t₀) hdet]

/-- If a nonzero scalar path has derivative `f(t₀) * c`, then its absolute
value has derivative `|f(t₀)| * c`.  This local sign argument avoids imposing
a global sign choice on the determinant. -/
theorem hasDerivAt_abs_of_self_mul
    {f : ℝ → ℝ} {t₀ c : ℝ}
    (hf : HasDerivAt f (f t₀ * c) t₀) (hne : f t₀ ≠ 0) :
    HasDerivAt (fun t => |f t|) (|f t₀| * c) t₀ := by
  rcases hne.lt_or_gt with hneg | hpos
  · have hlocal : (fun t => |f t|) =ᶠ[nhds t₀] fun t => -f t :=
      (hf.continuousAt.eventually (Iio_mem_nhds hneg)).mono
        (fun t ht => abs_of_neg ht)
    convert hf.neg.congr_of_eventuallyEq hlocal using 1
    simp [abs_of_neg hneg]
  · have hlocal : (fun t => |f t|) =ᶠ[nhds t₀] f :=
      (hf.continuousAt.eventually (Ioi_mem_nhds hpos)).mono
        (fun t ht => abs_of_pos ht)
    convert hf.congr_of_eventuallyEq hlocal using 1
    simp [abs_of_pos hpos]

/-- The coordinate density derivative at a nonsingular Gram matrix.  The
absolute value makes the formula independent of the determinant's local sign. -/
theorem hasDerivAt_chartVolumeDensity_of_det_ne_zero
    {n : ℕ} {G : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {G' : Matrix (Fin n) (Fin n) ℝ} {t₀ : ℝ}
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t₀)
    (hdetne : (G t₀).det ≠ 0) :
    HasDerivAt (fun t => chartVolumeDensity (n := n) (G t))
      ((1 / 2 : ℝ) * chartVolumeDensity (n := n) (G t₀) *
        ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i) t₀ := by
  have hdet := hasDerivAt_det_eq_det_mul_trace hG hdetne
  have habs : HasDerivAt (fun t => |(G t).det|)
      (|(G t₀).det| * ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i) t₀ :=
    hasDerivAt_abs_of_self_mul hdet hdetne
  have hsqrt := habs.sqrt (abs_ne_zero.mpr hdetne)
  have habspos : 0 < |(G t₀).det| := abs_pos.2 hdetne
  have hsqrtpos : 0 < Real.sqrt |(G t₀).det| := Real.sqrt_pos.2 habspos
  have hcoeff :
      (|(G t₀).det| * ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i) /
          (2 * Real.sqrt |(G t₀).det|) =
        (1 / 2 : ℝ) * Real.sqrt |(G t₀).det| *
          ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i := by
    field_simp
    rw [Real.sq_sqrt habspos.le]
    ring
  simpa [chartVolumeDensity, chartGramDet] using hsqrt.congr_deriv hcoeff

/-- The coordinate density derivative for a positive-definite Gram matrix.
The result is the usual one-half density times the inverse-matrix trace. -/
theorem hasDerivAt_chartVolumeDensity_of_posDef
    {n : ℕ} {G : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {G' : Matrix (Fin n) (Fin n) ℝ} {t₀ : ℝ}
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t₀)
    (hpos : (G t₀).PosDef) :
    HasDerivAt (fun t => chartVolumeDensity (n := n) (G t))
      ((1 / 2 : ℝ) * chartVolumeDensity (n := n) (G t₀) *
        ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i) t₀ := by
  have hdet_unit : IsUnit (G t₀).det :=
    (G t₀).isUnit_iff_isUnit_det.mp hpos.isUnit
  exact hasDerivAt_chartVolumeDensity_of_det_ne_zero hG hdet_unit.ne_zero

end VolumeDensity

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

namespace ClosedSmoothRiemannianMetric

/-- The coefficient matrix of the pointwise metric time derivative in the
canonical Gram frame based at `x`. -/
noncomputable def metricGramTimeDerivativeAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ :=
  fun i j => timeDerivAt gt t₀ x (gramFrame x x i) (gramFrame x x j)

/-- The chart-coordinate density of the fixed-fiber Gram matrix of `gt t` at
`x`. -/
noncomputable def coordinateGramVolumeDensityAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M) (t : ℝ) : ℝ :=
  VolumeDensity.chartVolumeDensity
    (n := Module.finrank ℝ (TM x)) (gramMatrix (gt t) x x)

omit [T2Space M] in
/-- Pointwise time differentiability of the metric differentiates every entry
of its canonical fixed-fiber Gram matrix with the expected coefficient. -/
theorem hasDerivAt_gramMatrix_time_entry
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    HasDerivAt (fun t => gramMatrix (gt t) x x i j)
      (metricGramTimeDerivativeAt gt t₀ x i j) t₀ := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  simpa [metricGramTimeDerivativeAt, gramMatrix, gramFrame, b, timeDerivAt] using
    (hgt (b i) (b j)).hasDerivAt

/-- The inverse-Gram contraction of the coefficient derivative is exactly the
intrinsic metric trace.  Symmetry removes the transpose appearing in the
generic Jacobi formula. -/
theorem inverseGram_contract_metricGramTimeDerivativeAt_eq_trace
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    (∑ i, ∑ j, (gramMatrix (gt t₀) x x)⁻¹ i j *
        metricGramTimeDerivativeAt gt t₀ x j i) =
      traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have htrace := traceMetricVariationAt_eq_sum_gram_inv
    (g := gt t₀) (h := timeDerivAt gt t₀) (x := x) (y := x)
    (gramMatrix_at_base_isUnit (g := gt t₀) (x := x))
    (timeDerivBilinAt gt t₀ x hgt) (by intro p q; rfl)
  rw [htrace]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [metricGramTimeDerivativeAt]
  rw [timeDerivAt_symm gt t₀ x (gramFrame x x j) (gramFrame x x i)]

/-- Coordinate Riemannian density first variation at a fixed point:
`d/dt sqrt(det g) = (1/2) sqrt(det g) tr_g(g')`.

This is the final finite-dimensional endpoint.  Identifying these local
densities with the Hausdorff-defined global `volumeMeasure`, gluing them across
charts, and differentiating their integral are intentionally not assumed here.
-/
theorem hasDerivAt_coordinateGramVolumeDensityAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    HasDerivAt (coordinateGramVolumeDensityAt gt x)
      ((1 / 2 : ℝ) * coordinateGramVolumeDensityAt gt x t₀ *
        traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x) t₀ := by
  have hdensity :=
    VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
      (G := fun t => gramMatrix (gt t) x x)
      (G' := metricGramTimeDerivativeAt gt t₀ x)
      (fun i j => hasDerivAt_gramMatrix_time_entry hgt i j)
      (gramMatrix_at_base_det_ne_zero (g := gt t₀) (x := x))
  have hcoeff :
      (1 / 2 : ℝ) *
          VolumeDensity.chartVolumeDensity (gramMatrix (gt t₀) x x) *
          (∑ i, ∑ j, (gramMatrix (gt t₀) x x)⁻¹ i j *
            metricGramTimeDerivativeAt gt t₀ x j i) =
        (1 / 2 : ℝ) *
          VolumeDensity.chartVolumeDensity (gramMatrix (gt t₀) x x) *
          traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x := by
    rw [inverseGram_contract_metricGramTimeDerivativeAt_eq_trace hgt]
  simpa [coordinateGramVolumeDensityAt] using hdensity.congr_deriv hcoeff

end ClosedSmoothRiemannianMetric

end Poincare
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Construct smooth cutoffs near compact coordinate sets"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients 51d21f04] Construct smooth cutoffs near compact coordinate sets
 1 file changed, 18 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:68:7: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  CompactSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:71:7: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  CompactSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:72:2: error: unsolved goals
case h
n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
p : M
K : Set E
hK : IsCompact K
hKU : K ⊆ (extChartAt I p).target
χ : E → ℝ
hχ : ContDiff ℝ ∞ χ
hχU : tsupport χ ⊆ (extChartAt I p).target
hone : ∀ z ∈ K, ∀ᶠ (y : E) in 𝓝 z, χ y = 1
right✝ : ∀ (z : E), χ z ∈ Icc 0 1
W : E → ℝ :=
  fun y => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
A : E → Matrix (Fin n) (Fin n) ℝ := fun y => (inverseChartPullbackGramMatrixField g p y)⁻¹
z : E
hz : z ∈ K
y : E
hy : χ y = 1
⊢ W y = ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:75:2: error: unsolved goals
case h
n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
p : M
K : Set E
hK : IsCompact K
hKU : K ⊆ (extChartAt I p).target
χ : E → ℝ
hχ : ContDiff ℝ ∞ χ
hχU : tsupport χ ⊆ (extChartAt I p).target
hone : ∀ z ∈ K, ∀ᶠ (y : E) in 𝓝 z, χ y = 1
right✝ : ∀ (z : E), χ z ∈ Icc 0 1
W : E → ℝ :=
  fun y => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
A : E → Matrix (Fin n) (Fin n) ℝ := fun y => (inverseChartPullbackGramMatrixField g p y)⁻¹
z : E
hz : z ∈ K
y : E
hy : χ y = 1
⊢ (fun i j => A y i j) = (inverseChartPullbackGramMatrixField g p y)⁻¹
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:79:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  χ ↑z
in the target expression
  (fun y => χ y * W y) ↑z = ↑(rawHausdorffLebesgueScale n) * inverseChartPullbackVolumeDensity g p z

case refine_5
n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
p : M
K : Set E
hK : IsCompact K
hKU : K ⊆ (extChartAt I p).target
χ : E → ℝ
hχ : ContDiff ℝ ∞ χ
hχU : tsupport χ ⊆ (extChartAt I p).target
hone : ∀ z ∈ K, ∀ᶠ (y : E) in 𝓝 z, χ y = 1
right✝ : ∀ (z : E), χ z ∈ Icc 0 1
W : E → ℝ :=
  fun y => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
A : E → Matrix (Fin n) (Fin n) ℝ := fun y => (inverseChartPullbackGramMatrixField g p y)⁻¹
z : ↑(extChartAt I p).target
hz : ↑z ∈ K
⊢ (fun y => χ y * W y) ↑z = ↑(rawHausdorffLebesgueScale n) * inverseChartPullbackVolumeDensity g p z
```

### Command

```sh
rg -n '[Dd]eriv.*(matrix|Matrix|nonsing|inv_entry)|[Dd]eriv.*inverse|inverse.*[Dd]eriv' Poincare/Global/MetricRaiseTimeDerivative.lean Poincare/Global/*Inverse* .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean; rg -n 'hasDerivAt.*line|hasFDerivAt.*line|HasFDerivAt.comp_hasDerivAt|HasDerivAt.*smul_const' .lake/packages/mathlib/Mathlib/Analysis/Calculus | head -30
```

Exit: 0

```text
Poincare/Global/DeTurckInverseGaugeODE.lean:114:      HasDerivAt beta (inverseGaugeExtendedField W DW (beta s)) s)
Poincare/Global/DeTurckInverseGaugeODE.lean:116:      HasDerivAt gamma (inverseGaugeExtendedField W DW (gamma s)) s)
Poincare/Global/DeTurckInverseGaugeODE.lean:232:Local inverse-gauge existence together with the Ricci pullback derivative.
Poincare/Global/DeTurckInverseGaugeODE.lean:240:theorem exists_local_inverseGauge_with_pullbackRicciDerivative
Poincare/Global/CartanFixedChartGenericInverseEndpointReduction.lean:124:derived from the generic inverse below.
Poincare/Global/CartanFixedChartGenericInverseEndpointReduction.lean:224:Moving-derivative continuity and the single inverse-endpoint identity produce
Poincare/Global/CartanFixedChartGenericInverseEndpointReduction.lean:284:/-- Per-center moving-derivative continuity and one generic-inverse endpoint
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:662:    HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:681:theorem fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:685:    HasStrictFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:686:  convert (analyticAt_inverse (𝕜 := 𝕜) x).hasStrictFDerivAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:687:  exact (fderiv_inverse x).symm
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:711:/-! ### Derivative of the inverse in a division ring
Poincare/Global/HausdorffInverseChartLocalPathLengthComparison.lean:76:theorem inverseChartCurve_enorm_mfderiv_eq_pullbackQuadraticForm
Poincare/Global/HausdorffInverseChartLocalPathLengthComparison.lean:93:  rw [GeodesicTransport.inverseChartCurve_enorm_mfderiv_eq_chartMetric
Poincare/Global/HausdorffInverseChartLocalPathLengthComparison.lean:133:  exact inverseChartCurve_enorm_mfderiv_eq_pullbackQuadraticForm
Poincare/Global/HausdorffFrozenInverseChartAreaFormula.lean:86:The inverse-chart derivative applied to the Euclidean frame is a genuine
Poincare/Global/HausdorffFrozenInverseChartAreaFormula.lean:87:tangent basis because the inverse-chart derivative is invertible on the
Poincare/Global/DeTurckBUCInverseGaugeEvolution.lean:1253:      inverse_fderiv := hUinvDeriv
Poincare/Global/DeTurckBUCInverseGaugeEvolution.lean:1435:      inverse_fderiv := hUinvDeriv
Poincare/Global/MetricRaiseTimeDerivative.lean:4:# Time derivative of the inverse metric
Poincare/Global/MetricRaiseTimeDerivative.lean:10:actual continuous-linear inverse metric, with derivative
Poincare/Global/MetricRaiseTimeDerivative.lean:234:/-- The inverse metric has its canonical derivative; no independent
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/AffineMap.lean:36:theorem hasDerivAtFilter : HasDerivAtFilter f (f.linear 1) L := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/AffineMap.lean:42:theorem hasDerivAt : HasDerivAt f (f.linear 1) x := f.hasDerivAtFilter
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/AffineMap.lean:68:theorem hasDerivAt_lineMap : HasDerivAt (lineMap a b) (b - a) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/AffineMap.lean:72:  hasDerivAt_lineMap.hasDerivWithinAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:60:theorem hasDerivAt_of_bilinear (hu : x ∈ tsupport v → HasDerivAt u u' x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:65:    · simpa using (B.hasFDerivAt_of_bilinear (hu hxv).hasFDerivAt (hv hxu).hasFDerivAt).hasDerivAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:93:  (B.hasDerivAt_of_bilinear (fun hx ↦ (hu hx).hasDerivAt) fun hx ↦ (hv hx).hasDerivAt).deriv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:151:theorem HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:19:* `HasFDerivAt.comp_hasDerivAt` etc: `f : E → F` composed with `g : 𝕜 → E`;
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:389:theorem HasFDerivAt.comp_hasDerivAt (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:395:theorem HasFDerivAt.comp_hasDerivAt_of_eq
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:926:  (hf.hasDerivAt.comp_semilinear σ' L).differentiableAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:281:  hf.hasFDerivAt.hasLineDerivAt _ |>.lineDifferentiableAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:285:  (hf.hasFDerivAt.hasLineDerivAt v).lineDeriv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:71:theorem IsBoundedBilinearMap.hasFDerivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:120:theorem ContinuousLinearMap.hasFDerivAt_of_bilinear {f : G' → E} {g : G' → F} {f' : G' →L[𝕜] E}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:145:  (B.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).fderiv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:270:      apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.const_add, HasDerivAt.smul_const,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:272:    · apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.smul_const, hasDerivAt_mul_const]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:273:    · apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.smul_const, hasDerivAt_mul_const]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:278:      apply_rules [HasDerivAt.hasDerivWithinAt, HasDerivAt.smul_const, hasDerivAt_id',
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:622:protected theorem hasFDerivAt [DecidableEq ι] : HasFDerivAt f (f.linearDeriv x) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:703:  simpa using (hasFDerivAt_const f x).continuousMultilinearMap_apply hg
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:866:theorem hasFDerivAt_uncurry_of_multilinear [DecidableEq ι]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:871:  (f ∘L .fst 𝕜 E (∀ i, G i)).hasFDerivAt.continuousMultilinearMap_apply
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:885:  (f.hasFDerivAt.comp_hasFDerivWithinAt x ha).continuousMultilinearMap_apply hb
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:897:  (f.hasFDerivAt.comp x ha).continuousMultilinearMap_apply hb
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:168:theorem hasFDerivAt (f : E [⋀^ι]→L[𝕜] F) (x : ι → E) : HasFDerivAt f (f.1.linearDeriv x) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:186:  (hc.hasFDerivAt.continuousMultilinear_apply_const u).fderiv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:206:  (hc.hasFDerivAt.continuousMultilinear_apply_const u).differentiableAt
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:76:2: error: unsolved goals
case h
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
p : M
K : Set E
hK : IsCompact K
hKU : K ⊆ (extChartAt I p).target
χ : E → ℝ
hχ : ContDiff ℝ ∞ χ
hχU : tsupport χ ⊆ (extChartAt I p).target
hone : ∀ z ∈ K, ∀ᶠ (y : E) in 𝓝 z, χ y = 1
right✝ : ∀ (z : E), χ z ∈ Icc 0 1
W : E → ℝ :=
  fun y => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
A : E → Matrix (Fin n) (Fin n) ℝ := fun y => (inverseChartPullbackGramMatrixField g p y)⁻¹
z : E
hz : z ∈ K
y : E
hy : χ y = 1
⊢ (fun i j => (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) = (inverseChartPullbackGramMatrixField g p y)⁻¹
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:75:31: warning: This simp argument is unused:
  A

Hint: Omit it from the simp argument list.
  simp only [hy, one_mul, W,̵ ̵A̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:78:28: warning: This simp argument is unused:
  W

Hint: Omit it from the simp argument list.
  simp only [hy, one_mul, W̵,̵ ̵A]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### Command

```sh
rg -n 'hessian.*(chart|Chart)|laplacian.*(chart|Chart)|gradient.*(chart|Chart)|trace.*(gram|Gram)' Poincare/Global/Laplacian.lean Poincare/Global/LeviCivitaTransport.lean Poincare/Global/MetricTrace.lean; rg -n 'inverse.*deriv|deriv.*inverse|inv.*deriv|deriv.*inv' Poincare/Global/Coordinate* Poincare/Global/Metric* | head -50
```

Exit: 0

```text
rg: Poincare/Global/MetricTrace.lean: No such file or directory (os error 2)
Poincare/Global/MetricFlowJointIteratedConnectionRegularity.lean:712:  have hfinv : (mfderiv Iₘ 𝓘(ℝ, E) f x).IsInvertible := by
Poincare/Global/MetricFlowJointIteratedConnectionRegularity.lean:739:    exact congrArg (mfderiv Iₘ 𝓘(ℝ, E) f y).inverse heq
Poincare/Global/CoordinateVolumeDensityVariation.lean:240:/-- The inverse-Gram contraction of the coefficient derivative is exactly the
Poincare/Global/MetricFlowJointConnectionRegularity.lean:10:three first spatial derivatives of the metric, and the inverse metric raises
Poincare/Global/MetricRaiseTimeDerivative.lean:4:# Time derivative of the inverse metric
Poincare/Global/MetricRaiseTimeDerivative.lean:10:actual continuous-linear inverse metric, with derivative
Poincare/Global/MetricRaiseTimeDerivative.lean:234:/-- The inverse metric has its canonical derivative; no independent
Poincare/Global/MetricFlowJointPinchingEvolution.lean:517:time derivative of the inverse metric.  This records exactly the reaction
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:8:inputs stop one derivative earlier: inverse-metric coefficients, Christoffel
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:826:theorem fderiv_inverse_apply_field
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:831:    fderiv ℝ (fun y ↦ (G y).inverse (P y)) z a =
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:832:      (G z).inverse (fderiv ℝ P z a) -
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:833:        (G z).inverse ((fderiv ℝ G z a) ((G z).inverse (P z))) := by
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:841:    hG hinv (P z)).fderiv
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:842:  have heval : (fderiv ℝ (fun y ↦ (G y).inverse) z a) (P z) =
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:843:      -((G z).inverse ((fderiv ℝ G z a) ((G z).inverse (P z)))) := by
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1055:    rw [fderiv_inverse_apply_field hGdiff
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1056:      (Filter.Eventually.of_forall hinv) hKG a, hKGderiv]
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1072:        (G z).inverse ((fderiv ℝ G z a)
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1074:    rw [fderiv_inverse_apply_field hGdiff
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1075:      (Filter.Eventually.of_forall hinv) hpsi a, hpsideriv]
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1081:        (G z).inverse ((fderiv ℝ G z a)
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1083:    rw [fderiv_inverse_apply_field hGdiff
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1084:      (Filter.Eventually.of_forall hinv) hKH a, hKHderiv]
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1101:    _ = -(fderiv ℝ (fun y ↦ (G y).inverse (psi y)) z a) +
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:1102:        fderiv ℝ (fun y ↦ (G y).inverse (KH y)) z a := by
Poincare/Global/CoordinateChartFrameDensityVariation.lean:13:then specializes it to `chartTangentBasisAt`, the inverse-chart derivative
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-3.lean
```

Exit: 1

```text
/tmp/stokes-global-evidence/dependencies-3.lean:76:2: error: unsolved goals
case h
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
p : M
K : Set E
hK : IsCompact K
hKU : K ⊆ (extChartAt I p).target
χ : E → ℝ
hχ : ContDiff ℝ ∞ χ
hχU : tsupport χ ⊆ (extChartAt I p).target
hone : ∀ z ∈ K, ∀ᶠ (y : E) in 𝓝 z, χ y = 1
right✝ : ∀ (z : E), χ z ∈ Icc 0 1
W : E → ℝ :=
  fun y => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
A : E → Matrix (Fin n) (Fin n) ℝ := fun y => (inverseChartPullbackGramMatrixField g p y)⁻¹
z : E
hz : z ∈ K
y : E
hy : χ y = 1
⊢ (fun i j => (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) = (inverseChartPullbackGramMatrixField g p y)⁻¹
/tmp/stokes-global-evidence/dependencies-3.lean:75:31: warning: This simp argument is unused:
  A

Hint: Omit it from the simp argument list.
  simp only [hy, one_mul, W,̵ ̵A̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/stokes-global-evidence/dependencies-3.lean:78:28: warning: This simp argument is unused:
  W

Hint: Omit it from the simp argument list.
  simp only [hy, one_mul, W̵,̵ ̵A]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹)) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W, A]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W, A]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:79:4: error: 'change' tactic failed, pattern
  χ y * A y i j = A y i j
is not definitionally equal to target
  χ y * A y i j = (inverseChartPullbackGramMatrixField g p y)⁻¹ i j
```

### Command

```sh
rg -n 'theorem.*(trace|hessian|gradient)|lemma.*(trace|hessian|gradient)' Poincare/Global/Laplacian.lean | head -45; sed -n '255,293p' .lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean; sed -n '650,704p' .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean; rg -n 'nonsing_inv_eq_ringInverse|ringInverse_eq|inv_eq_ringInverse' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix
```

Exit: 0

```text
81:theorem inner_gradientAt (g : ClosedSmoothRiemannianMetric n M)
101:theorem gradientAt_congr_of_eventuallyEq
115:theorem gradientAt_add (g : ClosedSmoothRiemannianMetric n M)
131:theorem gradient_add (g : ClosedSmoothRiemannianMetric n M)
139:theorem gradientAt_mul (g : ClosedSmoothRiemannianMetric n M)
153:theorem gradient_mul (g : ClosedSmoothRiemannianMetric n M)
161:theorem gradientAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
175:theorem gradient_const_smul (g : ClosedSmoothRiemannianMetric n M)
182:theorem gradientAt_const (g : ClosedSmoothRiemannianMetric n M)
191:theorem gradient_const (g : ClosedSmoothRiemannianMetric n M)
213:theorem mdifferentiableAt_gradient (g : ClosedSmoothRiemannianMetric n M)
403:theorem hessianAt_congr_of_eventuallyEq
445:theorem hessianDualAt_apply (g : ClosedSmoothRiemannianMetric n M)
461:theorem hessianContinuousAt_apply (g : ClosedSmoothRiemannianMetric n M)
466:theorem hessianDualAt_congr_of_eventuallyEq
495:theorem laplacianAt_eq_trace_hessianContinuousAt
541:theorem hessianAt_add (g : ClosedSmoothRiemannianMetric n M)
563:theorem hessianAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
575:theorem hessianAt_mul (g : ClosedSmoothRiemannianMetric n M)
602:theorem hessianContinuousAt_mul (g : ClosedSmoothRiemannianMetric n M)
617:theorem hessianAt_const (g : ClosedSmoothRiemannianMetric n M)
629:theorem hessianAt_symm (g : ClosedSmoothRiemannianMetric n M)
695:theorem hessianAt_symm' (g : ClosedSmoothRiemannianMetric n M)
702:theorem hessianDualAt_add (g : ClosedSmoothRiemannianMetric n M)
713:theorem hessianDualAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
721:theorem hessianDualAt_const (g : ClosedSmoothRiemannianMetric n M)

theorem LineDifferentiableWithinAt.lineDifferentiableAt (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (hs : s ∈ 𝓝 x) : LineDifferentiableAt 𝕜 f x v :=
  (h.hasLineDerivWithinAt.hasLineDerivAt hs).lineDifferentiableAt

lemma HasFDerivWithinAt.hasLineDerivWithinAt (hf : HasFDerivWithinAt f L s x) (v : E) :
    HasLineDerivWithinAt 𝕜 f (L v) s x v := by
  let F := fun (t : 𝕜) ↦ x + t • v
  rw [show x = F (0 : 𝕜) by simp [F]] at hf
  have A : HasDerivWithinAt F (0 + (1 : 𝕜) • v) (F ⁻¹' s) 0 :=
    ((hasDerivAt_const (0 : 𝕜) x).add ((hasDerivAt_id' (0 : 𝕜)).smul_const v)).hasDerivWithinAt
  simp only [one_smul, zero_add] at A
  exact hf.comp_hasDerivWithinAt (x := (0 : 𝕜)) A (mapsTo_preimage F s)

theorem DifferentiableWithinAt.lineDifferentiableWithinAt
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  hf.hasFDerivWithinAt.hasLineDerivWithinAt _ |>.lineDifferentiableWithinAt

lemma HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt f L x) (v : E) :
    HasLineDerivAt 𝕜 f (L v) x v := by
  rw [← hasLineDerivWithinAt_univ]
  exact hf.hasFDerivWithinAt.hasLineDerivWithinAt v

theorem DifferentiableAt.lineDifferentiableAt (hf : DifferentiableAt 𝕜 f x) :
    LineDifferentiableAt 𝕜 f x v :=
  hf.hasFDerivAt.hasLineDerivAt _ |>.lineDifferentiableAt

lemma DifferentiableAt.lineDeriv_eq_fderiv (hf : DifferentiableAt 𝕜 f x) :
    lineDeriv 𝕜 f x v = fderiv 𝕜 f x v :=
  (hf.hasFDerivAt.hasLineDerivAt v).lineDeriv

theorem LineDifferentiableWithinAt.mono_of_mem_nhdsWithin (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (hst : s ∈ 𝓝[t] x) : LineDifferentiableWithinAt 𝕜 f t x v :=
  (h.hasLineDerivWithinAt.mono_of_mem_nhdsWithin hst).lineDifferentiableWithinAt

theorem lineDerivWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    lineDerivWithin 𝕜 f s x v = lineDeriv 𝕜 f x v := by
  apply derivWithin_of_mem_nhds

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`.

TODO (low prio): prove a version without assumption `[HasSummableGeomSeries R]` but within the set
of units. -/
@[fun_prop]
theorem hasFDerivAt_ringInverse (x : Rˣ) :
    HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
  have : (fun t : R => Ring.inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] id :=
    (inverse_add_norm_diff_second_order x).trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  simpa [hasFDerivAt_iff_isLittleO_nhds_zero] using this

@[fun_prop]
theorem differentiableAt_inverse {x : R} (hx : IsUnit x) :
    DifferentiableAt 𝕜 (@Ring.inverse R _) x :=
  let ⟨u, hu⟩ := hx; hu ▸ (hasFDerivAt_ringInverse u).differentiableAt

@[fun_prop]
theorem differentiableWithinAt_inverse {x : R} (hx : IsUnit x) (s : Set R) :
    DifferentiableWithinAt 𝕜 (@Ring.inverse R _) s x :=
  (differentiableAt_inverse hx).differentiableWithinAt

@[fun_prop]
theorem differentiableOn_inverse : DifferentiableOn 𝕜 (@Ring.inverse R _) {x | IsUnit x} :=
  fun _x hx => differentiableWithinAt_inverse hx _

theorem fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
  (hasFDerivAt_ringInverse x).fderiv

theorem hasStrictFDerivAt_ringInverse (x : Rˣ) :
    HasStrictFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
  convert (analyticAt_inverse (𝕜 := 𝕜) x).hasStrictFDerivAt
  exact (fderiv_inverse x).symm

variable {h : E → R} {z : E} {S : Set E}

@[fun_prop]
theorem DifferentiableWithinAt.inverse (hf : DifferentiableWithinAt 𝕜 h S z) (hz : IsUnit (h z)) :
    DifferentiableWithinAt 𝕜 (fun x => (h x)⁻¹ʳ) S z :=
  (differentiableAt_inverse hz).comp_differentiableWithinAt z hf

@[simp, fun_prop]
theorem DifferentiableAt.inverse (hf : DifferentiableAt 𝕜 h z) (hz : IsUnit (h z)) :
    DifferentiableAt 𝕜 (fun x => (h x)⁻¹ʳ) z :=
  (differentiableAt_inverse hz).comp z hf

@[fun_prop]
theorem DifferentiableOn.inverse (hf : DifferentiableOn 𝕜 h S) (hz : ∀ x ∈ S, IsUnit (h x)) :
    DifferentiableOn 𝕜 (fun x => (h x)⁻¹ʳ) S := fun x h => (hf x h).inverse (hz x h)

.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:200:    simp_rw [nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ hA, Ring.inverse_non_unit _ hD,
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:217:    simp_rw [nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ hA, Ring.inverse_non_unit _ hD,
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:195:theorem nonsing_inv_eq_ringInverse : A⁻¹ = A⁻¹ʳ := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:567:  rw [nonsing_inv_eq_ringInverse]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:635:  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_add_inverse h
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:640:  simpa only [nonsing_inv_eq_ringInverse] using Ring.inverse_sub_inverse h
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:729:    simp_rw [nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ this,
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-3.lean
```

Exit: 1

```text
/tmp/stokes-global-evidence/dependencies-3.lean:79:4: error: 'change' tactic failed, pattern
  χ y * A y i j = A y i j
is not definitionally equal to target
  χ y * A y i j = (inverseChartPullbackGramMatrixField g p y)⁻¹ i j
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹)) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
```

### Command

```sh
rg -n 'theorem.*(inv|mul_inv|inv_mul)|def inv ' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean | head -25; rg -n '^def HasLineDerivAt|^theorem HasLineDerivAt' .lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean
```

Exit: 0

```text
86:theorem invOf_eq [Invertible A.det] [Invertible A] : ⅟A = ⅟A.det • A.adjugate := by
109:theorem det_invOf [Invertible A] [Invertible A.det] : (⅟A).det = ⅟A.det := by
137:theorem isUnit_det_of_invertible [Invertible A] : IsUnit A.det :=
142:theorem isUnit_det_of_left_inverse (h : B * A = 1) : IsUnit A.det :=
145:theorem isUnit_det_of_right_inverse (h : A * B = 1) : IsUnit A.det :=
148:theorem det_ne_zero_of_left_inverse [Nontrivial α] (h : B * A = 1) : A.det ≠ 0 :=
151:theorem det_ne_zero_of_right_inverse [Nontrivial α] (h : A * B = 1) : A.det ≠ 0 :=
172:theorem inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate :=
175:theorem nonsing_inv_apply_not_isUnit (h : ¬IsUnit A.det) : A⁻¹ = 0 := by
178:theorem nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate := by
183:theorem invOf_eq_nonsing_inv [Invertible A] : ⅟A = A⁻¹ := by
190:theorem coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ : Matrix n n α) := by
195:theorem nonsing_inv_eq_ringInverse : A⁻¹ = A⁻¹ʳ := by
202:theorem transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹ := by
205:theorem conjTranspose_nonsing_inv [StarRing α] : A⁻¹ᴴ = Aᴴ⁻¹ := by
211:theorem mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1 := by
217:theorem nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1 := by
226:theorem inv_inv_of_invertible [Invertible A] : A⁻¹⁻¹ = A := by
230:theorem mul_nonsing_inv_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A * A⁻¹ = B := by
234:theorem mul_nonsing_inv_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A * (A⁻¹ * B) = B := by
238:theorem nonsing_inv_mul_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A⁻¹ * A = B := by
242:theorem nonsing_inv_mul_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A⁻¹ * (A * B) = B := by
246:theorem mul_inv_of_invertible [Invertible A] : A * A⁻¹ = 1 :=
250:theorem inv_mul_of_invertible [Invertible A] : A⁻¹ * A = 1 :=
254:theorem mul_inv_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B * A * A⁻¹ = B :=
80:def HasLineDerivAt (f : E → F) (f' : F) (x : E) (v : E) :=
126:theorem HasLineDerivAt.lineDifferentiableAt (hf : HasLineDerivAt 𝕜 f f' x v) :
156:theorem HasLineDerivAt.unique (h₀ : HasLineDerivAt 𝕜 f f₀' x v) (h₁ : HasLineDerivAt 𝕜 f f₁' x v) :
220:theorem HasLineDerivAt.tendsto_slope_zero_right [Preorder 𝕜] (h : HasLineDerivAt 𝕜 f f' x v) :
224:theorem HasLineDerivAt.tendsto_slope_zero_left [Preorder 𝕜] (h : HasLineDerivAt 𝕜 f f' x v) :
363:theorem HasLineDerivAt.congr_of_eventuallyEq (h : HasLineDerivAt 𝕜 f f' x v) (h₁ : f₁ =ᶠ[𝓝 x] f) :
394:theorem HasLineDerivAt.le_of_lip' {f : E → F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
408:theorem HasLineDerivAt.le_of_lipschitzOn
417:theorem HasLineDerivAt.le_of_lipschitz
483:theorem HasLineDerivAt.of_comp {v : E'} (hf : HasLineDerivAt 𝕜 (f ∘ L) f' x v) :
514:theorem HasLineDerivAt.smul (h : HasLineDerivAt 𝕜 f f' x v) (c : 𝕜) :
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-3.lean
```

Exit: 0

```text
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
```

### Command

```sh
rg -n 'scoped.*(Norm|norm)|namespace.*Norm|NormedRing|NormedAlgebra' .lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean | head -55; rg -n 'HasFDerivAt.*apply|fderiv_apply' .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean | head -35
```

Exit: 0

```text
15:* The elementwise norm (with `open scoped Matrix.Norms.Elementwise`):
23:* The Frobenius norm (with `open scoped Matrix.Norms.Frobenius`):
28:  * `Matrix.frobeniusNormedRing`
29:  * `Matrix.frobeniusNormedAlgebra`
33:* The $L^\infty$ operator norm (with `open scoped Matrix.Norms.Operator`):
40:  * `Matrix.linftyOpNonUnitalSemiNormedRing`
41:  * `Matrix.linftyOpSemiNormedRing`
42:  * `Matrix.linftyOpNonUnitalNormedRing`
43:  * `Matrix.linftyOpNormedRing`
44:  * `Matrix.linftyOpNormedAlgebra`
51:`Mathlib/Analysis/CStarAlgebra/Matrix.lean` and `open scoped Matrix.Norms.L2Operator`.
208:namespace Norms.Elementwise
362:protected def linftyOpNonUnitalSemiNormedRing [NonUnitalSeminormedRing α] :
376:protected def linftyOpSemiNormedRing [SeminormedRing α] [DecidableEq n] :
378:  { Matrix.linftyOpNonUnitalSemiNormedRing, Matrix.instRing with }
384:protected def linftyOpNonUnitalNormedRing [NonUnitalNormedRing α] :
385:    NonUnitalNormedRing (Matrix n n α) :=
386:  { Matrix.linftyOpNonUnitalSemiNormedRing with
393:protected def linftyOpNormedRing [NormedRing α] [DecidableEq n] : NormedRing (Matrix n n α) :=
394:  { Matrix.linftyOpSemiNormedRing with
401:protected def linftyOpNormedAlgebra [NormedField R] [SeminormedRing α] [NormedAlgebra R α]
402:    [DecidableEq n] : NormedAlgebra R (Matrix n n α) :=
407:variable [NormedDivisionRing α] [NormedAlgebra ℝ α]
432:variable [NontriviallyNormedField α] [NormedAlgebra ℝ α]
470:namespace Norms.Operator
477:  Matrix.linftyOpNonUnitalSemiNormedRing
478:  Matrix.linftyOpSemiNormedRing
479:  Matrix.linftyOpNonUnitalNormedRing
480:  Matrix.linftyOpNormedRing
481:  Matrix.linftyOpNormedAlgebra
653:def frobeniusNormedRing [DecidableEq m] : NormedRing (Matrix m m α) :=
662:def frobeniusNormedAlgebra [DecidableEq m] [NormedField R] [NormedAlgebra R α] :
663:    NormedAlgebra R (Matrix m m α) :=
670:namespace Norms.Frobenius
675:  Matrix.frobeniusNormedRing
676:  Matrix.frobeniusNormedAlgebra
490:theorem fderiv_apply (hΦ : DifferentiableAt 𝕜 Φ x) (i : ι) :
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Extend genuine chart coefficients smoothly near compact sets"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients 97e1acec] Extend genuine chart coefficients smoothly near compact sets
 1 file changed, 42 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:88:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
rg -n 'HasLineDerivAt|hasLineDerivAt' Poincare/Global/Heat* | head -12; sed -n '75,86p' .lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean; sed -n '475,500p' .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean; rg -n 'sum_swap|sum_comm' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean | head -10
```

Exit: 0

```text

/-- `f` has the derivative `f'` at the point `x` along the direction `v`.
That is, `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`.
Note that this definition is less well behaved than the total Fréchet derivative, which
should generally be favored over this one. -/
def HasLineDerivAt (f : E → F) (f' : F) (x : E) (v : E) :=
  HasDerivAt (fun t ↦ f (x + t • v)) f' (0 : 𝕜)

/-- `f` is line-differentiable at the point `x` in the direction `v` in the set `s` if there
exists `f'` such that `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
def LineDifferentiableWithinAt (f : E → F) (s : Set E) (x : E) (v : E) : Prop :=
-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
theorem fderivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (φ i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => fderivWithin 𝕜 (φ i) s x :=
  (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).fderivWithin hs

theorem fderiv_pi (h : ∀ i, DifferentiableAt 𝕜 (φ i) x) :
    fderiv 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x :=
  (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).fderiv

theorem fderivWithin_apply (hΦ : DifferentiableWithinAt 𝕜 Φ s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (i : ι) :
    fderivWithin 𝕜 (fun x => Φ x i) s x = (proj i).comp (fderivWithin 𝕜 Φ s x) :=
  (hasFDerivWithinAt_pi'.1 hΦ.hasFDerivWithinAt i).fderivWithin hs

theorem fderiv_apply (hΦ : DifferentiableAt 𝕜 Φ x) (i : ι) :
    fderiv 𝕜 (fun x => Φ x i) x = (proj i).comp (fderiv 𝕜 Φ x) :=
  (hasFDerivAt_pi'.1 hΦ.hasFDerivAt i).fderiv

end Pi

/-!
### Derivatives of tuples `f : E → Π i : Fin n.succ, F' i`

These can be used to prove results about functions of the form `fun x ↦ ![f x, g x, h x]`,
as `Matrix.vecCons` is defeq to `Fin.cons`.
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-4.lean
```

Exit: 0

```text
/tmp/stokes-global-evidence/dependencies-4.lean:88:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Shrink finite chart covers with compact coordinate closures"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients 602e53b5] Shrink finite chart covers with compact coordinate closures
 1 file changed, 23 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
rg -n 'differentiable.*matrix|matrix.*ifferentiable|contDiff.*matrix|matrix.*ontDiff|hasFDerivAt.*matrix' .lake/packages/mathlib/Mathlib/Analysis/Matrix .lake/packages/mathlib/Mathlib/Analysis/Calculus; sed -n '30,90p' Poincare/Global/MetricRaiseTimeDerivative.lean; rg -n 'hasFDerivAt.*inv|fderiv.*inv' .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Inverse.lean
```

Exit: 2

```text
local notation "TM" => (TangentSpace I : M → Type _)

omit [T2Space M] in
/-- A finite matrix-valued path is differentiable when every entry is. -/
theorem differentiableAt_matrix_det_of_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun t ↦ A t i j) t₀) :
    DifferentiableAt ℝ (fun t ↦ (A t).det) t₀ := by
  classical
  rw [show (fun t : ℝ ↦ (A t).det) =
      fun t : ℝ ↦ ∑ σ : Equiv.Perm ι,
        ((↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A t (σ i) i) by
    funext t
    rw [Matrix.det_apply']]
  have hsum : DifferentiableAt ℝ
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
        fun t : ℝ ↦ (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A t (σ i) i) t₀ := by
    refine DifferentiableAt.sum (u := (Finset.univ : Finset (Equiv.Perm ι))) ?_
    intro σ _hσ
    have hprod : DifferentiableAt ℝ
        (∏ i ∈ (Finset.univ : Finset ι), fun t : ℝ ↦ A t (σ i) i) t₀ := by
      refine DifferentiableAt.finsetProd (u := (Finset.univ : Finset ι)) ?_
      intro i _hi
      exact hA (σ i) i
    have hprod' : DifferentiableAt ℝ (fun t : ℝ ↦ ∏ i, A t (σ i) i) t₀ :=
      hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ by simp)
    have hconst : DifferentiableAt ℝ
        (fun _ : ℝ ↦ (↑↑(Equiv.Perm.sign σ) : ℝ)) t₀ := differentiableAt_const _
    simpa using hconst.mul hprod'
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ by simp)

omit [T2Space M] in
/-- An adjugate entry of a finite matrix-valued path is differentiable when
all matrix entries are. -/
theorem differentiableAt_matrix_adjugate_entry_of_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun t ↦ A t i j) t₀)
    (i j : ι) :
    DifferentiableAt ℝ (fun t ↦ (A t).adjugate i j) t₀ := by
  classical
  let row : ι → ℝ := Pi.single i (1 : ℝ)
  let B : ℝ → Matrix ι ι ℝ := fun t ↦ (A t).updateRow j row
  have hentries : ∀ a b,
      DifferentiableAt ℝ (fun t ↦ B t a b) t₀ := by
    intro a b
    by_cases ha : a = j
    · subst a
      simpa [B, Matrix.updateRow] using
        (differentiableAt_const t₀ (row b))
    · simpa [B, Matrix.updateRow, ha] using hA a b
  have hdet : DifferentiableAt ℝ (fun t ↦ (B t).det) t₀ :=
    differentiableAt_matrix_det_of_entries hentries
  exact hdet.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ by
    simp [B, row, Matrix.adjugate_apply])

omit [T2Space M] in
/-- An inverse-matrix entry is differentiable at an invertible base matrix. -/
theorem differentiableAt_matrix_inv_entry_of_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
rg: .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Inverse.lean: IO error for operation on .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Inverse.lean: No such file or directory (os error 2)
```

### Command

```sh
sed -n "85,180p" Poincare/Global/MetricRaiseTimeDerivative.lean && sed -n "195,290p" Poincare/Global/MetricRaiseTimeDerivative.lean
```

Exit: 0

```text
    simp [B, row, Matrix.adjugate_apply])

omit [T2Space M] in
/-- An inverse-matrix entry is differentiable at an invertible base matrix. -/
theorem differentiableAt_matrix_inv_entry_of_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun t ↦ A t i j) t₀)
    (hdet : (A t₀).det ≠ 0) (i j : ι) :
    DifferentiableAt ℝ (fun t ↦ (A t)⁻¹ i j) t₀ := by
  have hdetDiff : DifferentiableAt ℝ (fun t ↦ (A t).det) t₀ :=
    differentiableAt_matrix_det_of_entries hA
  have hdetInv : DifferentiableAt ℝ (fun t ↦ ((A t).det)⁻¹) t₀ :=
    hdetDiff.inv hdet
  have hadj : DifferentiableAt ℝ (fun t ↦ (A t).adjugate i j) t₀ :=
    differentiableAt_matrix_adjugate_entry_of_entries hA i j
  exact (hdetInv.mul hadj).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ by simp [Matrix.inv_def])

/-- Every entry of the time-dependent Gram matrix on one fixed tangent fiber
is differentiable under `TimeDifferentiableAt`. -/
theorem gramMatrix_time_entry_differentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    DifferentiableAt ℝ (fun t ↦
      gramMatrix (gt t) x x i j) t₀ := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  simpa [gramMatrix, b] using hgt (b i) (b j)

/-- Every inverse-Gram entry on one fixed tangent fiber is differentiable in
time. -/
theorem gramMatrix_time_inv_entry_differentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    DifferentiableAt ℝ (fun t ↦
      (gramMatrix (gt t) x x)⁻¹ i j) t₀ := by
  apply differentiableAt_matrix_inv_entry_of_entries
    (fun a b ↦ gramMatrix_time_entry_differentiableAt hgt a b)
  exact gramMatrix_at_base_det_ne_zero
    (g := gt t₀) (x := x)

/-- Differentiability of an operator-valued real path can be checked after
applying every fixed input when the operator domain is finite-dimensional. -/
theorem differentiableAt_clm_path_of_apply
    {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ → V →L[ℝ] F} {t₀ : ℝ}
    (h : ∀ v : V, DifferentiableAt ℝ (fun t ↦ Φ t v) t₀) :
    DifferentiableAt ℝ Φ t₀ := by
  let b := Module.finBasis ℝ V
  let coordC : Fin (Module.finrank ℝ V) → (V →L[ℝ] ℝ) :=
    fun i ↦ LinearMap.toContinuousLinearMap (b.coord i)
  have hrepr : ∀ ρ : V →L[ℝ] F,
      ρ = ∑ i, (coordC i).smulRight (ρ (b i)) := by
    intro ρ
    ext v
    have hv := b.sum_repr v
    conv_lhs => rw [← hv]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, map_smul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show coordC i v = b.coord i v from rfl, Module.Basis.coord_apply]
  have hfun : Φ = fun t ↦ ∑ i, (coordC i).smulRight (Φ t (b i)) := by
    funext t
    exact hrepr (Φ t)
  rw [hfun]
  refine DifferentiableAt.fun_sum ?_
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ V F (coordC i)).differentiableAt
    |>.comp t₀ (h (b i))

/-- The raised image of a fixed covector is differentiable in time. -/
theorem metricRaiseContinuousAt_apply_differentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) (φ : TM x →L[ℝ] ℝ) :
    DifferentiableAt ℝ
      (fun t ↦ (gt t).metricRaiseContinuousAt x φ) t₀ := by
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let coordC : Fin (Module.finrank ℝ (TM x)) → (TM x →L[ℝ] ℝ) :=
    fun i ↦ LinearMap.toContinuousLinearMap (b.coord i)
  have hcoord : ∀ i,
      DifferentiableAt ℝ
        (fun t ↦ (gt t).metricRaiseContinuousAt x (coordC i)) t₀ := by
    intro i
    ext v
    have hv := b.sum_repr v
    conv_lhs => rw [← hv]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show coordC i v = b.coord i v from rfl, Module.Basis.coord_apply]
    ring
  have hfun :
      (fun t ↦ (gt t).metricRaiseContinuousAt x φ) =
        fun t ↦ ∑ i, φ (b i) •
          (gt t).metricRaiseContinuousAt x (coordC i) := by
    funext t
    conv_lhs => rw [hφ]
    rw [map_sum]
    simp
  rw [hfun]
  refine DifferentiableAt.fun_sum ?_
  intro i _
  exact (hcoord i).const_smul (φ (b i))

/-- Pointwise differentiability of a metric family automatically gives
differentiability of the actual continuous-linear index-raising map. -/
theorem metricRaiseContinuousAt_differentiableAt_of_timeDifferentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    DifferentiableAt ℝ (fun t ↦ (gt t).metricRaiseContinuousAt x) t₀ := by
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  apply differentiableAt_clm_path_of_apply
  exact metricRaiseContinuousAt_apply_differentiableAt hgt

set_option synthInstance.maxHeartbeats 100000

/-- The inverse metric has its canonical derivative; no independent
`hRaise` witness is required. -/
theorem hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x)
      (metricRaiseDerivAt gt t₀ x hgt) t₀ := by
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have hdiff : DifferentiableAt ℝ
      (fun t ↦ (gt t).metricRaiseContinuousAt x) t₀ :=
    metricRaiseContinuousAt_differentiableAt_of_timeDifferentiableAt hgt
  have hderiv : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x)
      (deriv (fun t ↦ (gt t).metricRaiseContinuousAt x) t₀) t₀ :=
    (hasDerivAt_deriv_iff (𝕜 := ℝ)
      (f := fun t ↦ (gt t).metricRaiseContinuousAt x) (x := t₀)).2 hdiff
  have heq := metricRaise_deriv_eq_of_hasDerivAt hgt hderiv
  rw [heq] at hderiv
  exact hderiv

end Poincare
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-5.lean
```

Exit: 0

```text
/tmp/stokes-global-evidence/dependencies-5.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.LineDeriv.Basic

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
theorem fderiv_chartWeight
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) :
    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
    (G := fun t : ℝ ↦ G (z + t • v))
    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hdet)
  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Differentiate the genuine chart weight in spatial directions"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients 3d89675d] Differentiate the genuine chart weight in spatial directions
 1 file changed, 30 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:169:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (?a + ?b) * ?c
in the target expression
  (fun T => T * B) (Q * A t + B * D) = (fun T => T * B) 0

n : ℕ
A : ℝ → Matrix (Fin n) (Fin n) ℝ
t : ℝ
hA : ∀ (i j : Fin n), DifferentiableAt ℝ (fun s => A s i j) t
hdet : (A t).det ≠ 0
i j : Fin n
B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
D : Matrix (Fin n) (Fin n) ℝ := fun k l => deriv (fun s => A s k l) t
Q : Matrix (Fin n) (Fin n) ℝ := fun k l => deriv (fun s => (A s)⁻¹ k l) t
hB : ∀ (k l : Fin n), DifferentiableAt ℝ (fun s => (A s)⁻¹ k l) t
hlocal : ∀ᶠ (s : ℝ) in 𝓝 t, (A s).det ≠ 0
hprod : Q * A t + B * D = 0
hab : A t * B = 1
hh : (fun T => T * B) (Q * A t + B * D) = (fun T => T * B) 0
⊢ Q = -(B * D * B)
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:172:2: error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
```

### Command

```sh
rg -n 'eventually_ne|eq_neg_of_add_eq_zero_left|HasDerivAt.fun_sum|HasDerivAt.unique|HasDerivAt.congr_of_eventuallyEq' .lake/packages/mathlib/Mathlib/Topology .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv .lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean | head -30
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:396:theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:612:theorem HasDerivAt.congr_of_eventuallyEq (h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:211:theorem HasDerivAt.fun_sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:234:  (HasDerivAt.fun_sum fun i hi ↦ (h i hi).hasDerivAt).deriv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:97:theorem HasDerivWithinAt.eventually_ne (h : HasDerivWithinAt f f' s x) (hf' : f' ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:99:  h.hasFDerivWithinAt.eventually_ne ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:111:theorem HasDerivAt.eventually_ne (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:113:  simpa only [compl_eq_univ_diff] using (hasDerivWithinAt_univ.2 h).eventually_ne hf'
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inverse.lean:126:    exact hf.hasDerivWithinAt.eventually_ne h
.lake/packages/mathlib/Mathlib/Topology/Bornology/Absorbs.lean:144:  (eventually_ne_cobounded 0).mono fun a ha ↦ by rw [smul_set_univ₀ ha]; apply subset_univ
.lake/packages/mathlib/Mathlib/Topology/Bornology/Absorbs.lean:148:  eventually_congr <| (eventually_ne_cobounded 0).mono fun c hc ↦ by
.lake/packages/mathlib/Mathlib/Topology/Bornology/Basic.lean:242:lemma eventually_ne_cobounded (a : α) : ∀ᶠ x in cobounded α, x ≠ a :=
.lake/packages/mathlib/Mathlib/Topology/Bornology/Basic.lean:243:  le_cofinite_iff_eventually_ne.1 (le_cofinite _) a
.lake/packages/mathlib/Mathlib/Topology/Bornology/Basic.lean:257:nonrec lemma Filter.Tendsto.eventually_ne_cobounded [Bornology α] {f : β → α} {l : Filter β}
.lake/packages/mathlib/Mathlib/Topology/Bornology/Basic.lean:259:  h.eventually <| eventually_ne_cobounded a
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:200:  exact (hg.eventually_ne hy).mono fun n hn => mul_div_cancel_right₀ _ hn
.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Continuity.lean:50:theorem eventually_ne_nhdsWithin {x} (hx : x ∈ e.source) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Ideals.lean:263:      have := (map_continuous g).continuousAt.eventually_ne hgx
.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean:681:theorem Filter.Tendsto.eventually_ne {X} [TopologicalSpace Y] [T1Space Y] {g : X → Y}
.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean:685:theorem ContinuousAt.eventually_ne [TopologicalSpace Y] [T1Space Y] {g : X → Y} {x : X} {y : Y}
.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean:687:  hg1.tendsto.eventually_ne hg2
.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean:689:theorem eventually_ne_nhds [T1Space X] {a b : X} (h : a ≠ b) : ∀ᶠ x in 𝓝 a, x ≠ b :=
.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean:692:theorem eventually_ne_nhdsWithin [T1Space X] {a b : X} {s : Set X} (h : a ≠ b) :
.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean:694:  Filter.Eventually.filter_mono nhdsWithin_le_nhds <| eventually_ne_nhds h
.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean:868:  exacts [self_mem_nhdsWithin, eventually_ne_nhdsWithin hx]
.lake/packages/mathlib/Mathlib/Topology/Separation/Hausdorff.lean:629:theorem ContinuousAt.ne_iff_eventually_ne [T2Space Y] {x : X} {f g : X → Y}
.lake/packages/mathlib/Mathlib/Topology/Separation/Hausdorff.lean:657:        ((hf.ne_iff_eventually_ne hg).1 hCon)).and hfg
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/TsumUniformlyOn.lean:84:  · filter_upwards with t r hr using HasDerivAt.fun_sum
.lake/packages/mathlib/Mathlib/Topology/Algebra/AsymptoticCone.lean:97:      filter_upwards [tendsto_fst.eventually (eventually_ne_atTop 0)] with _ h
.lake/packages/mathlib/Mathlib/Topology/Algebra/AsymptoticCone.lean:122:    filter_upwards [eventually_ne_atTop 0] with _ h
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
rg -n '(inverseChartPullbackGramMatrixField.*symm|inverseChartPullbackGramMatrix.*symm|IsSymm.*inv|IsHermitian.*inv|theorem.*isHermitian|lemma.*isHermitian)' Poincare .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean | head -35; rg -n 'IsSymm|isSymm' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Symmetric.lean | head -35
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:297:lemma IsSymm.inv {A : Matrix n n α} (hA : A.IsSymm) : A⁻¹.IsSymm :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:76:theorem isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:112:protected lemma zero : PosSemidef (0 : Matrix n n R) := ⟨isHermitian_zero, by simp⟩
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:165:theorem isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian :=
Poincare/Global/HausdorffInverseChartGramContinuity.lean:120:    (inverseChartPullbackGramMatrix_eq_field g x₀ z).symm
18:* `Matrix.isSymm`: a matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`.
33:def IsSymm (A : Matrix n n α) : Prop :=
36:instance (A : Matrix n n α) [Decidable (Aᵀ = A)] : Decidable (IsSymm A) :=
39:theorem IsSymm.eq {A : Matrix n n α} (h : A.IsSymm) : Aᵀ = A :=
43:theorem IsSymm.ext_iff {A : Matrix n n α} : A.IsSymm ↔ ∀ i j, A j i = A i j :=
47:theorem IsSymm.ext {A : Matrix n n α} : (∀ i j, A j i = A i j) → A.IsSymm :=
50:theorem IsSymm.apply {A : Matrix n n α} (h : A.IsSymm) (i j : n) : A j i = A i j :=
51:  IsSymm.ext_iff.1 h i j
53:theorem isSymm_mul_transpose_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
54:    (A * Aᵀ).IsSymm :=
57:theorem isSymm_transpose_mul_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
58:    (Aᵀ * A).IsSymm :=
61:theorem isSymm_add_transpose_self [AddCommSemigroup α] (A : Matrix n n α) : (A + Aᵀ).IsSymm :=
64:theorem isSymm_transpose_add_self [AddCommSemigroup α] (A : Matrix n n α) : (Aᵀ + A).IsSymm :=
68:theorem isSymm_zero [Zero α] : (0 : Matrix n n α).IsSymm :=
72:theorem isSymm_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsSymm :=
75:theorem IsSymm.pow [CommSemiring α] [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsSymm)
77:    (A ^ k).IsSymm := by
78:  rw [IsSymm, transpose_pow, h]
81:theorem IsSymm.map {A : Matrix n n α} (h : A.IsSymm) (f : α → β) : (A.map f).IsSymm := by
82:  rw [IsSymm, ← transpose_map, h.eq]
85:theorem isSymm_map_iff {A : Matrix n n α} {f : α → β} (hf : f.Injective) :
86:    (A.map f).IsSymm ↔ A.IsSymm := by
87:  rw [IsSymm, IsSymm, ← transpose_map, map_injective hf |>.eq_iff]
89:theorem IsSymm.transpose {A : Matrix n n α} (h : A.IsSymm) : Aᵀ.IsSymm :=
93:theorem isSymm_transpose_iff {A : Matrix n n α} : Aᵀ.IsSymm ↔ A.IsSymm := by
99:theorem IsSymm.conjTranspose [Star α] {A : Matrix n n α} (h : A.IsSymm) : Aᴴ.IsSymm :=
103:theorem isSymm_conjTranspose_iff [InvolutiveStar α] {A : Matrix n n α} : Aᴴ.IsSymm ↔ A.IsSymm := by
109:theorem IsSymm.neg [Neg α] {A : Matrix n n α} (h : A.IsSymm) : (-A).IsSymm :=
113:theorem isSymm_neg_iff [InvolutiveNeg α] {A : Matrix n n α} : (-A).IsSymm ↔ A.IsSymm := by
119:theorem IsSymm.add {A B : Matrix n n α} [Add α] (hA : A.IsSymm) (hB : B.IsSymm) : (A + B).IsSymm :=
123:theorem IsSymm.sub {A B : Matrix n n α} [Sub α] (hA : A.IsSymm) (hB : B.IsSymm) : (A - B).IsSymm :=
127:theorem IsSymm.smul [SMul R α] {A : Matrix n n α} (h : A.IsSymm) (k : R) : (k • A).IsSymm :=
131:theorem isSymm_smul_iff [Monoid R] [MulAction R α] {A : Matrix n n α} (k : R) [Invertible k] :
132:    (k • A).IsSymm ↔ A.IsSymm := by
```

### Command

```sh
rg -n 'sum_univ_three|sum_univ_succ' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean; rg -n 'IsHermitian.*isSymm|isHermitian_iff_isSymm|isSymm.*isHermitian' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix
```

Exit: 1

```text
606:        simp_rw [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one,
655:        simp_rw [Fin.sum_univ_succ, Fin.cons_succ]
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-6.lean
```

Exit: 0

```text
/tmp/stokes-global-evidence/dependencies-6.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.LineDeriv.Basic

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
theorem fderiv_chartWeight
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) :
    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
    (G := fun t : ℝ ↦ G (z + t • v))
    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hdet)
  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq

/-- Differentiating the inverse identity gives the full inverse-matrix derivative. -/
theorem deriv_matrix_inv_entry {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s ↦ A s i j) t)
    (hdet : (A t).det ≠ 0) (i j : Fin n) :
    deriv (fun s ↦ (A s)⁻¹ i j) t =
      -(∑ k, ∑ l, (A t)⁻¹ i k * deriv (fun s ↦ A s k l) t * (A t)⁻¹ l j) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
  let D : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ A s k l) t
  let Q : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ (A s)⁻¹ k l) t
  have hB (k l : Fin n) : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹ k l) t :=
    differentiableAt_matrix_inv_entry_of_entries hA hdet k l
  have hlocal : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 :=
    (differentiableAt_matrix_det_of_entries hA).continuousAt.eventually_ne hdet
  have hprod : Q * A t + B * D = 0 := by
    ext k l
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun m _ ↦ (hB k m).hasDerivAt.mul (hA m l).hasDerivAt)
    have heq : (fun s ↦ ∑ m, (A s)⁻¹ k m * A s m l) =ᶠ[𝓝 t]
        (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ) k l) := by
      filter_upwards [hlocal] with s hs
      exact congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T k l)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
    have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib, Q, B, D] using hzero
  have hab : A t * B = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hq : Q = -(B * D * B) := by
    have hh := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T * B) hprod
    dsimp only at hh
    rw [add_mul, Matrix.mul_assoc, hab, mul_one, zero_mul] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hentry := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T i j) hq
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, Q, B, D] at hentry
  rw [Finset.sum_comm] at hentry
  exact hentry

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Derive the inverse-matrix entry derivative from the inverse identity"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients fd96c61b] Derive the inverse-matrix entry derivative from the inverse identity
 1 file changed, 37 insertions(+)
```

### Command

```sh
rg -n '(theorem|lemma).*sum_univ_three|(theorem|lemma).*sum_univ_succ|theorem.*IsHermitian.*apply|lemma.*IsHermitian.*apply|conjTranspose_eq_transpose' .lake/packages/mathlib/Mathlib | head -25
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Hermitian.lean:35:lemma IsHermitian.coe_re_apply_self (h : A.IsHermitian) (i : n) : (re (A i i) : 𝕜) = A i i := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean:60:theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:353:theorem conjTranspose_eq_transpose_of_trivial [Star α] [TrivialStar α] (A : Matrix m n α) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean:124:  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix]
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:193:92: error: Invalid field notation: Identifier or numeral expected
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:184:62: error: unsolved goals
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
p : M
z : E
hz : z ∈ (extChartAt I p).target
v : E
i j : Fin n
G : E → Matrix (Fin n) (Fin n) ℝ := inverseChartPullbackGramMatrixField g p
hG : ∀ (k l : Fin n), DifferentiableAt ℝ (fun y => G y k l) z
hdet : (G z).det ≠ 0
⊢ (fderiv ℝ (fun y => (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z) v =
    -∑ k,
        ∑ l,
          (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
              (fderiv ℝ (fun y => inverseChartPullbackGramMatrixField g p y k l) z) v *
            (inverseChartPullbackGramMatrixField g p z)⁻¹ l j
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/algebra.lean
```

Exit: 1

```text
/tmp/stokes-global-evidence/algebra.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/stokes-global-evidence/algebra.lean:193:92: error: Invalid field notation: Identifier or numeral expected
/tmp/stokes-global-evidence/algebra.lean:184:62: error: unsolved goals
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
p : M
z : E
hz : z ∈ (extChartAt I p).target
v : E
i j : Fin n
G : E → Matrix (Fin n) (Fin n) ℝ := inverseChartPullbackGramMatrixField g p
hG : ∀ (k l : Fin n), DifferentiableAt ℝ (fun y => G y k l) z
hdet : (G z).det ≠ 0
⊢ (fderiv ℝ (fun y => (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z) v =
    -∑ k,
        ∑ l,
          (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
              (fderiv ℝ (fun y => inverseChartPullbackGramMatrixField g p y k l) z) v *
            (inverseChartPullbackGramMatrixField g p z)⁻¹ l j
/tmp/stokes-global-evidence/algebra.lean:207:25: error(lean.unknownIdentifier): Unknown identifier `k`

Note: It is not possible to treat `k` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
/tmp/stokes-global-evidence/algebra.lean:207:33: error(lean.unknownIdentifier): Unknown identifier `k`

Note: It is not possible to treat `k` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
/tmp/stokes-global-evidence/algebra.lean:212:4: error: `simp` made no progress
/tmp/stokes-global-evidence/algebra.lean:212:4: error: `simp` made no progress
/tmp/stokes-global-evidence/algebra.lean:212:4: error: `simp` made no progress
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/algebra.lean
```

Exit: 1

```text
/tmp/stokes-global-evidence/algebra.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/stokes-global-evidence/algebra.lean:211:4: error: `simp` made no progress
/tmp/stokes-global-evidence/algebra.lean:211:4: error: `simp` made no progress
/tmp/stokes-global-evidence/algebra.lean:211:4: error: `simp` made no progress
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-7.lean
```

Exit: 0

```text
/tmp/stokes-global-evidence/dependencies-7.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.LineDeriv.Basic

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
theorem fderiv_chartWeight
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) :
    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
    (G := fun t : ℝ ↦ G (z + t • v))
    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hdet)
  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq

/-- Differentiating the inverse identity gives the full inverse-matrix derivative. -/
theorem deriv_matrix_inv_entry {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s ↦ A s i j) t)
    (hdet : (A t).det ≠ 0) (i j : Fin n) :
    deriv (fun s ↦ (A s)⁻¹ i j) t =
      -(∑ k, ∑ l, (A t)⁻¹ i k * deriv (fun s ↦ A s k l) t * (A t)⁻¹ l j) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
  let D : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ A s k l) t
  let Q : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ (A s)⁻¹ k l) t
  have hB (k l : Fin n) : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹ k l) t :=
    differentiableAt_matrix_inv_entry_of_entries hA hdet k l
  have hlocal : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 :=
    (differentiableAt_matrix_det_of_entries hA).continuousAt.eventually_ne hdet
  have hprod : Q * A t + B * D = 0 := by
    ext k l
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun m _ ↦ (hB k m).hasDerivAt.mul (hA m l).hasDerivAt)
    have heq : (fun s ↦ ∑ m, (A s)⁻¹ k m * A s m l) =ᶠ[𝓝 t]
        (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ) k l) := by
      filter_upwards [hlocal] with s hs
      exact congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T k l)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
    have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib, Q, B, D] using hzero
  have hab : A t * B = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hq : Q = -(B * D * B) := by
    have hh := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T * B) hprod
    dsimp only at hh
    rw [add_mul, Matrix.mul_assoc, hab, mul_one, zero_mul] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hentry := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T i j) hq
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, Q, B, D] at hentry
  rw [Finset.sum_comm] at hentry
  exact hentry

/-- The inverse Gram entries have the usual spatial derivative. -/
theorem fderiv_chartInverseMetric
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) (i j : Fin n) :
    fderiv ℝ (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z v =
      -(∑ k, ∑ l, (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
        fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y k l) z v *
        (inverseChartPullbackGramMatrixField g p z)⁻¹ l j) := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (k l : Fin n) : DifferentiableAt ℝ (fun y ↦ G y k l) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p k l z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hInv := (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hd := deriv_matrix_inv_entry (A := fun s : ℝ ↦ G (z + s • v)) (t := 0)
    (fun k l ↦ ((hG k l).hasFDerivAt.hasLineDerivAt v).differentiableAt)
    (by simpa only [zero_smul, add_zero] using hdet) i j
  rw [(hInv.hasFDerivAt.hasLineDerivAt v).deriv] at hd
  simp only [zero_smul, add_zero] at hd
  simpa only [((hG _ _).hasFDerivAt.hasLineDerivAt v).deriv] using hd

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric
```

### Command

```sh
rg -n 'prod_univ_three|prod_univ_succ|prod_univ_zero' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin* .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean | head -20
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:20:and `Fin.prod_univ_succ`, and the formula `Fin.prod_const` for the product of a
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:61:theorem prod_univ_zero (f : Fin 0 → M) : ∏ i, f i = 1 :=
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:68:theorem prod_univ_succAbove (f : Fin (n + 1) → M) (x : Fin (n + 1)) :
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:76:theorem prod_univ_succ (f : Fin (n + 1) → M) :
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:78:  prod_univ_succAbove f 0
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:86:  simpa [mul_comm] using prod_univ_succAbove f (last n)
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:100:  simp_rw [prod_univ_succ, cons_zero, cons_succ]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:112:  simp [prod_univ_succ]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:119:theorem prod_univ_three (f : Fin 3 → M) : ∏ i, f i = f 0 * f 1 * f 2 := by
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:125:  rw [prod_univ_castSucc, prod_univ_three]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:451:    rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:664:          Fin.prod_univ_succ, Fin.castLE_zero, Fin.cons_zero, ← Nat.div_div_eq_div_mul,
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:667:        exact ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq (Fin.prod_univ_succ _)))
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:762:    rw [Fin.prod_univ_succ]; simp
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:768:        { rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Differentiate the inverse Gram entries in spatial directions"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients e25cb170] Differentiate the inverse Gram entries in spatial directions
 1 file changed, 24 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:208:55: error: unsolved goals
case «0»
a : Matrix (Fin 3) (Fin 3) ℝ
ha : a.IsSymm
D : Fin 3 → Fin 3 → Fin 3 → ℝ
w : ℝ
⊢ w * a 0 0 * D 0 0 0 * a 0 ⟨0, ⋯⟩ * (-1 / 2) - w * a 0 0 * D 0 0 1 * a 1 ⟨0, ⋯⟩ - w * a 0 0 * D 0 0 2 * a 2 ⟨0, ⋯⟩ +
                                                                                        w * a 0 0 * a 1 ⟨0, ⋯⟩ *
                                                                                            D 1 0 0 *
                                                                                          (1 / 2) +
                                                                                      w * a 0 0 * a 2 ⟨0, ⋯⟩ * D 2 0 0 *
                                                                                        (1 / 2) +
                                                                                    w * a 0 1 * D 0 1 0 * a 0 ⟨0, ⋯⟩ *
                                                                                      (-1 / 2) +
                                                                                  w * a 0 1 * D 0 0 1 * a 0 ⟨0, ⋯⟩ *
                                                                                    (1 / 2) -
                                                                                w * a 0 1 * D 0 1 1 * a 1 ⟨0, ⋯⟩ -
                                                                              w * a 0 1 * D 0 1 2 * a 2 ⟨0, ⋯⟩ -
                                                                            w * a 0 1 * a 0 ⟨0, ⋯⟩ * D 1 0 0 +
                                                                          w * a 0 1 * a 1 ⟨0, ⋯⟩ * D 1 1 0 * (1 / 2) +
                                                                        w * a 0 1 * a 1 ⟨0, ⋯⟩ * D 1 0 1 * (-1 / 2) -
                                                                      w * a 0 1 * a 2 ⟨0, ⋯⟩ * D 1 0 2 +
                                                                    w * a 0 1 * a 2 ⟨0, ⋯⟩ * D 2 1 0 * (1 / 2) +
                                                                  w * a 0 1 * a 2 ⟨0, ⋯⟩ * D 2 0 1 * (1 / 2) +
                                                                w * a 0 2 * D 0 2 0 * a 0 ⟨0, ⋯⟩ * (-1 / 2) -
                                                              w * a 0 2 * D 0 2 1 * a 1 ⟨0, ⋯⟩ +
                                                            w * a 0 2 * D 0 0 2 * a 0 ⟨0, ⋯⟩ * (1 / 2) -
                                                          w * a 0 2 * D 0 2 2 * a 2 ⟨0, ⋯⟩ -
                                                        w * a 0 2 * a 0 ⟨0, ⋯⟩ * D 2 0 0 +
                                                      w * a 0 2 * a 1 ⟨0, ⋯⟩ * D 1 2 0 * (1 / 2) +
                                                    w * a 0 2 * a 1 ⟨0, ⋯⟩ * D 1 0 2 * (1 / 2) -
                                                  w * a 0 2 * a 1 ⟨0, ⋯⟩ * D 2 0 1 +
                                                w * a 0 2 * a 2 ⟨0, ⋯⟩ * D 2 2 0 * (1 / 2) +
                                              w * a 0 2 * a 2 ⟨0, ⋯⟩ * D 2 0 2 * (-1 / 2) +
                                            w * a 1 1 * D 0 1 1 * a 0 ⟨0, ⋯⟩ * (1 / 2) -
                                          w * a 1 1 * a 0 ⟨0, ⋯⟩ * D 1 1 0 +
                                        w * a 1 1 * a 1 ⟨0, ⋯⟩ * D 1 1 1 * (-1 / 2) -
                                      w * a 1 1 * a 2 ⟨0, ⋯⟩ * D 1 1 2 +
                                    w * a 1 1 * a 2 ⟨0, ⋯⟩ * D 2 1 1 * (1 / 2) +
                                  w * a 1 2 * D 0 2 1 * a 0 ⟨0, ⋯⟩ * (1 / 2) +
                                w * a 1 2 * D 0 1 2 * a 0 ⟨0, ⋯⟩ * (1 / 2) -
                              w * a 1 2 * a 0 ⟨0, ⋯⟩ * D 1 2 0 -
                            w * a 1 2 * a 0 ⟨0, ⋯⟩ * D 2 1 0 +
                          w * a 1 2 * a 1 ⟨0, ⋯⟩ * D 1 2 1 * (-1 / 2) +
                        w * a 1 2 * a 1 ⟨0, ⋯⟩ * D 1 1 2 * (1 / 2) -
                      w * a 1 2 * a 1 ⟨0, ⋯⟩ * D 2 1 1 -
                    w * a 1 2 * a 2 ⟨0, ⋯⟩ * D 1 2 2 +
                  w * a 1 2 * a 2 ⟨0, ⋯⟩ * D 2 2 1 * (1 / 2) +
                w * a 1 2 * a 2 ⟨0, ⋯⟩ * D 2 1 2 * (-1 / 2) +
              w * a 2 2 * D 0 2 2 * a 0 ⟨0, ⋯⟩ * (1 / 2) -
            w * a 2 2 * a 0 ⟨0, ⋯⟩ * D 2 2 0 +
          w * a 2 2 * a 1 ⟨0, ⋯⟩ * D 1 2 2 * (1 / 2) -
        w * a 2 2 * a 1 ⟨0, ⋯⟩ * D 2 2 1 +
      w * a 2 2 * a 2 ⟨0, ⋯⟩ * D 2 2 2 * (-1 / 2) =
    w * a 0 0 * D 0 0 0 * a ⟨0, ⋯⟩ 0 * (-1 / 2) - w * a 0 0 * D 0 0 1 * a ⟨0, ⋯⟩ 1 - w * a 0 0 * D 0 0 2 * a ⟨0, ⋯⟩ 2 +
                                                                                        w * a 0 0 * D 1 0 0 *
                                                                                            a ⟨0, ⋯⟩ 1 *
                                                                                          (1 / 2) +
                                                                                      w * a 0 0 * D 2 0 0 * a ⟨0, ⋯⟩ 2 *
                                                                                        (1 / 2) +
                                                                                    w * a 0 1 * D 0 1 0 * a ⟨0, ⋯⟩ 0 *
                                                                                      (-1 / 2) +
                                                                                  w * a 0 1 * D 0 0 1 * a ⟨0, ⋯⟩ 0 *
                                                                                    (1 / 2) -
                                                                                w * a 0 1 * D 0 1 1 * a ⟨0, ⋯⟩ 1 -
                                                                              w * a 0 1 * D 0 1 2 * a ⟨0, ⋯⟩ 2 -
                                                                            w * a 0 1 * D 1 0 0 * a ⟨0, ⋯⟩ 0 +
                                                                          w * a 0 1 * D 1 1 0 * a ⟨0, ⋯⟩ 1 * (1 / 2) +
                                                                        w * a 0 1 * D 1 0 1 * a ⟨0, ⋯⟩ 1 * (-1 / 2) -
                                                                      w * a 0 1 * D 1 0 2 * a ⟨0, ⋯⟩ 2 +
                                                                    w * a 0 1 * D 2 1 0 * a ⟨0, ⋯⟩ 2 * (1 / 2) +
                                                                  w * a 0 1 * D 2 0 1 * a ⟨0, ⋯⟩ 2 * (1 / 2) +
                                                                w * a 0 2 * D 0 2 0 * a ⟨0, ⋯⟩ 0 * (-1 / 2) -
                                                              w * a 0 2 * D 0 2 1 * a ⟨0, ⋯⟩ 1 +
                                                            w * a 0 2 * D 0 0 2 * a ⟨0, ⋯⟩ 0 * (1 / 2) -
                                                          w * a 0 2 * D 0 2 2 * a ⟨0, ⋯⟩ 2 +
                                                        w * a 0 2 * D 1 2 0 * a ⟨0, ⋯⟩ 1 * (1 / 2) +
                                                      w * a 0 2 * D 1 0 2 * a ⟨0, ⋯⟩ 1 * (1 / 2) -
                                                    w * a 0 2 * D 2 0 0 * a ⟨0, ⋯⟩ 0 +
                                                  w * a 0 2 * D 2 2 0 * a ⟨0, ⋯⟩ 2 * (1 / 2) -
                                                w * a 0 2 * D 2 0 1 * a ⟨0, ⋯⟩ 1 +
                                              w * a 0 2 * D 2 0 2 * a ⟨0, ⋯⟩ 2 * (-1 / 2) +
                                            w * a 1 1 * D 0 1 1 * a ⟨0, ⋯⟩ 0 * (1 / 2) -
                                          w * a 1 1 * D 1 1 0 * a ⟨0, ⋯⟩ 0 +
                                        w * a 1 1 * D 1 1 1 * a ⟨0, ⋯⟩ 1 * (-1 / 2) -
                                      w * a 1 1 * D 1 1 2 * a ⟨0, ⋯⟩ 2 +
                                    w * a 1 1 * D 2 1 1 * a ⟨0, ⋯⟩ 2 * (1 / 2) +
                                  w * a 1 2 * D 0 2 1 * a ⟨0, ⋯⟩ 0 * (1 / 2) +
                                w * a 1 2 * D 0 1 2 * a ⟨0, ⋯⟩ 0 * (1 / 2) -
                              w * a 1 2 * D 1 2 0 * a ⟨0, ⋯⟩ 0 +
                            w * a 1 2 * D 1 2 1 * a ⟨0, ⋯⟩ 1 * (-1 / 2) +
                          w * a 1 2 * D 1 1 2 * a ⟨0, ⋯⟩ 1 * (1 / 2) -
                        w * a 1 2 * D 1 2 2 * a ⟨0, ⋯⟩ 2 -
                      w * a 1 2 * D 2 1 0 * a ⟨0, ⋯⟩ 0 -
                    w * a 1 2 * D 2 1 1 * a ⟨0, ⋯⟩ 1 +
                  w * a 1 2 * D 2 2 1 * a ⟨0, ⋯⟩ 2 * (1 / 2) +
                w * a 1 2 * D 2 1 2 * a ⟨0, ⋯⟩ 2 * (-1 / 2) +
              w * a 2 2 * D 0 2 2 * a ⟨0, ⋯⟩ 0 * (1 / 2) +
            w * a 2 2 * D 1 2 2 * a ⟨0, ⋯⟩ 1 * (1 / 2) -
          w * a 2 2 * D 2 2 0 * a ⟨0, ⋯⟩ 0 -
        w * a 2 2 * D 2 2 1 * a ⟨0, ⋯⟩ 1 +
      w * a 2 2 * D 2 2 2 * a ⟨0, ⋯⟩ 2 * (-1 / 2)

case «1»
a : Matrix (Fin 3) (Fin 3) ℝ
ha : a.IsSymm
D : Fin 3 → Fin 3 → Fin 3 → ℝ
w : ℝ
⊢ w * a 0 0 * D 0 0 0 * a 0 ⟨1, ⋯⟩ * (-1 / 2) - w * a 0 0 * D 0 0 1 * a 1 ⟨1, ⋯⟩ - w * a 0 0 * D 0 0 2 * a 2 ⟨1, ⋯⟩ +
                                                                                        w * a 0 0 * a 1 ⟨1, ⋯⟩ *
                                                                                            D 1 0 0 *
                                                                                          (1 / 2) +
                                                                                      w * a 0 0 * a 2 ⟨1, ⋯⟩ * D 2 0 0 *
                                                                                        (1 / 2) +
                                                                                    w * a 0 1 * D 0 1 0 * a 0 ⟨1, ⋯⟩ *
                                                                                      (-1 / 2) +
                                                                                  w * a 0 1 * D 0 0 1 * a 0 ⟨1, ⋯⟩ *
                                                                                    (1 / 2) -
                                                                                w * a 0 1 * D 0 1 1 * a 1 ⟨1, ⋯⟩ -
                                                                              w * a 0 1 * D 0 1 2 * a 2 ⟨1, ⋯⟩ -
                                                                            w * a 0 1 * a 0 ⟨1, ⋯⟩ * D 1 0 0 +
                                                                          w * a 0 1 * a 1 ⟨1, ⋯⟩ * D 1 1 0 * (1 / 2) +
                                                                        w * a 0 1 * a 1 ⟨1, ⋯⟩ * D 1 0 1 * (-1 / 2) -
                                                                      w * a 0 1 * a 2 ⟨1, ⋯⟩ * D 1 0 2 +
                                                                    w * a 0 1 * a 2 ⟨1, ⋯⟩ * D 2 1 0 * (1 / 2) +
                                                                  w * a 0 1 * a 2 ⟨1, ⋯⟩ * D 2 0 1 * (1 / 2) +
                                                                w * a 0 2 * D 0 2 0 * a 0 ⟨1, ⋯⟩ * (-1 / 2) -
                                                              w * a 0 2 * D 0 2 1 * a 1 ⟨1, ⋯⟩ +
                                                            w * a 0 2 * D 0 0 2 * a 0 ⟨1, ⋯⟩ * (1 / 2) -
                                                          w * a 0 2 * D 0 2 2 * a 2 ⟨1, ⋯⟩ -
                                                        w * a 0 2 * a 0 ⟨1, ⋯⟩ * D 2 0 0 +
                                                      w * a 0 2 * a 1 ⟨1, ⋯⟩ * D 1 2 0 * (1 / 2) +
                                                    w * a 0 2 * a 1 ⟨1, ⋯⟩ * D 1 0 2 * (1 / 2) -
                                                  w * a 0 2 * a 1 ⟨1, ⋯⟩ * D 2 0 1 +
                                                w * a 0 2 * a 2 ⟨1, ⋯⟩ * D 2 2 0 * (1 / 2) +
                                              w * a 0 2 * a 2 ⟨1, ⋯⟩ * D 2 0 2 * (-1 / 2) +
                                            w * a 1 1 * D 0 1 1 * a 0 ⟨1, ⋯⟩ * (1 / 2) -
                                          w * a 1 1 * a 0 ⟨1, ⋯⟩ * D 1 1 0 +
                                        w * a 1 1 * a 1 ⟨1, ⋯⟩ * D 1 1 1 * (-1 / 2) -
                                      w * a 1 1 * a 2 ⟨1, ⋯⟩ * D 1 1 2 +
                                    w * a 1 1 * a 2 ⟨1, ⋯⟩ * D 2 1 1 * (1 / 2) +
                                  w * a 1 2 * D 0 2 1 * a 0 ⟨1, ⋯⟩ * (1 / 2) +
                                w * a 1 2 * D 0 1 2 * a 0 ⟨1, ⋯⟩ * (1 / 2) -
                              w * a 1 2 * a 0 ⟨1, ⋯⟩ * D 1 2 0 -
                            w * a 1 2 * a 0 ⟨1, ⋯⟩ * D 2 1 0 +
                          w * a 1 2 * a 1 ⟨1, ⋯⟩ * D 1 2 1 * (-1 / 2) +
                        w * a 1 2 * a 1 ⟨1, ⋯⟩ * D 1 1 2 * (1 / 2) -
                      w * a 1 2 * a 1 ⟨1, ⋯⟩ * D 2 1 1 -
                    w * a 1 2 * a 2 ⟨1, ⋯⟩ * D 1 2 2 +
                  w * a 1 2 * a 2 ⟨1, ⋯⟩ * D 2 2 1 * (1 / 2) +
                w * a 1 2 * a 2 ⟨1, ⋯⟩ * D 2 1 2 * (-1 / 2) +
              w * a 2 2 * D 0 2 2 * a 0 ⟨1, ⋯⟩ * (1 / 2) -
            w * a 2 2 * a 0 ⟨1, ⋯⟩ * D 2 2 0 +
          w * a 2 2 * a 1 ⟨1, ⋯⟩ * D 1 2 2 * (1 / 2) -
        w * a 2 2 * a 1 ⟨1, ⋯⟩ * D 2 2 1 +
      w * a 2 2 * a 2 ⟨1, ⋯⟩ * D 2 2 2 * (-1 / 2) =
    w * a 0 0 * D 0 0 0 * a ⟨1, ⋯⟩ 0 * (-1 / 2) - w * a 0 0 * D 0 0 1 * a ⟨1, ⋯⟩ 1 - w * a 0 0 * D 0 0 2 * a ⟨1, ⋯⟩ 2 +
                                                                                        w * a 0 0 * D 1 0 0 *
                                                                                            a ⟨1, ⋯⟩ 1 *
                                                                                          (1 / 2) +
                                                                                      w * a 0 0 * D 2 0 0 * a ⟨1, ⋯⟩ 2 *
                                                                                        (1 / 2) +
                                                                                    w * a 0 1 * D 0 1 0 * a ⟨1, ⋯⟩ 0 *
                                                                                      (-1 / 2) +
                                                                                  w * a 0 1 * D 0 0 1 * a ⟨1, ⋯⟩ 0 *
                                                                                    (1 / 2) -
                                                                                w * a 0 1 * D 0 1 1 * a ⟨1, ⋯⟩ 1 -
                                                                              w * a 0 1 * D 0 1 2 * a ⟨1, ⋯⟩ 2 -
                                                                            w * a 0 1 * D 1 0 0 * a ⟨1, ⋯⟩ 0 +
                                                                          w * a 0 1 * D 1 1 0 * a ⟨1, ⋯⟩ 1 * (1 / 2) +
                                                                        w * a 0 1 * D 1 0 1 * a ⟨1, ⋯⟩ 1 * (-1 / 2) -
                                                                      w * a 0 1 * D 1 0 2 * a ⟨1, ⋯⟩ 2 +
                                                                    w * a 0 1 * D 2 1 0 * a ⟨1, ⋯⟩ 2 * (1 / 2) +
                                                                  w * a 0 1 * D 2 0 1 * a ⟨1, ⋯⟩ 2 * (1 / 2) +
                                                                w * a 0 2 * D 0 2 0 * a ⟨1, ⋯⟩ 0 * (-1 / 2) -
                                                              w * a 0 2 * D 0 2 1 * a ⟨1, ⋯⟩ 1 +
                                                            w * a 0 2 * D 0 0 2 * a ⟨1, ⋯⟩ 0 * (1 / 2) -
                                                          w * a 0 2 * D 0 2 2 * a ⟨1, ⋯⟩ 2 +
                                                        w * a 0 2 * D 1 2 0 * a ⟨1, ⋯⟩ 1 * (1 / 2) +
                                                      w * a 0 2 * D 1 0 2 * a ⟨1, ⋯⟩ 1 * (1 / 2) -
                                                    w * a 0 2 * D 2 0 0 * a ⟨1, ⋯⟩ 0 +
                                                  w * a 0 2 * D 2 2 0 * a ⟨1, ⋯⟩ 2 * (1 / 2) -
                                                w * a 0 2 * D 2 0 1 * a ⟨1, ⋯⟩ 1 +
                                              w * a 0 2 * D 2 0 2 * a ⟨1, ⋯⟩ 2 * (-1 / 2) +
                                            w * a 1 1 * D 0 1 1 * a ⟨1, ⋯⟩ 0 * (1 / 2) -
                                          w * a 1 1 * D 1 1 0 * a ⟨1, ⋯⟩ 0 +
                                        w * a 1 1 * D 1 1 1 * a ⟨1, ⋯⟩ 1 * (-1 / 2) -
                                      w * a 1 1 * D 1 1 2 * a ⟨1, ⋯⟩ 2 +
                                    w * a 1 1 * D 2 1 1 * a ⟨1, ⋯⟩ 2 * (1 / 2) +
                                  w * a 1 2 * D 0 2 1 * a ⟨1, ⋯⟩ 0 * (1 / 2) +
                                w * a 1 2 * D 0 1 2 * a ⟨1, ⋯⟩ 0 * (1 / 2) -
                              w * a 1 2 * D 1 2 0 * a ⟨1, ⋯⟩ 0 +
                            w * a 1 2 * D 1 2 1 * a ⟨1, ⋯⟩ 1 * (-1 / 2) +
                          w * a 1 2 * D 1 1 2 * a ⟨1, ⋯⟩ 1 * (1 / 2) -
                        w * a 1 2 * D 1 2 2 * a ⟨1, ⋯⟩ 2 -
                      w * a 1 2 * D 2 1 0 * a ⟨1, ⋯⟩ 0 -
                    w * a 1 2 * D 2 1 1 * a ⟨1, ⋯⟩ 1 +
                  w * a 1 2 * D 2 2 1 * a ⟨1, ⋯⟩ 2 * (1 / 2) +
                w * a 1 2 * D 2 1 2 * a ⟨1, ⋯⟩ 2 * (-1 / 2) +
              w * a 2 2 * D 0 2 2 * a ⟨1, ⋯⟩ 0 * (1 / 2) +
            w * a 2 2 * D 1 2 2 * a ⟨1, ⋯⟩ 1 * (1 / 2) -
          w * a 2 2 * D 2 2 0 * a ⟨1, ⋯⟩ 0 -
        w * a 2 2 * D 2 2 1 * a ⟨1, ⋯⟩ 1 +
      w * a 2 2 * D 2 2 2 * a ⟨1, ⋯⟩ 2 * (-1 / 2)

case «2»
a : Matrix (Fin 3) (Fin 3) ℝ
ha : a.IsSymm
D : Fin 3 → Fin 3 → Fin 3 → ℝ
w : ℝ
⊢ w * a 0 0 * D 0 0 0 * a 0 ⟨2, ⋯⟩ * (-1 / 2) - w * a 0 0 * D 0 0 1 * a 1 ⟨2, ⋯⟩ - w * a 0 0 * D 0 0 2 * a 2 ⟨2, ⋯⟩ +
                                                                                        w * a 0 0 * a 1 ⟨2, ⋯⟩ *
                                                                                            D 1 0 0 *
                                                                                          (1 / 2) +
                                                                                      w * a 0 0 * a 2 ⟨2, ⋯⟩ * D 2 0 0 *
                                                                                        (1 / 2) +
                                                                                    w * a 0 1 * D 0 1 0 * a 0 ⟨2, ⋯⟩ *
                                                                                      (-1 / 2) +
                                                                                  w * a 0 1 * D 0 0 1 * a 0 ⟨2, ⋯⟩ *
                                                                                    (1 / 2) -
                                                                                w * a 0 1 * D 0 1 1 * a 1 ⟨2, ⋯⟩ -
                                                                              w * a 0 1 * D 0 1 2 * a 2 ⟨2, ⋯⟩ -
                                                                            w * a 0 1 * a 0 ⟨2, ⋯⟩ * D 1 0 0 +
                                                                          w * a 0 1 * a 1 ⟨2, ⋯⟩ * D 1 1 0 * (1 / 2) +
                                                                        w * a 0 1 * a 1 ⟨2, ⋯⟩ * D 1 0 1 * (-1 / 2) -
                                                                      w * a 0 1 * a 2 ⟨2, ⋯⟩ * D 1 0 2 +
                                                                    w * a 0 1 * a 2 ⟨2, ⋯⟩ * D 2 1 0 * (1 / 2) +
                                                                  w * a 0 1 * a 2 ⟨2, ⋯⟩ * D 2 0 1 * (1 / 2) +
                                                                w * a 0 2 * D 0 2 0 * a 0 ⟨2, ⋯⟩ * (-1 / 2) -
                                                              w * a 0 2 * D 0 2 1 * a 1 ⟨2, ⋯⟩ +
                                                            w * a 0 2 * D 0 0 2 * a 0 ⟨2, ⋯⟩ * (1 / 2) -
                                                          w * a 0 2 * D 0 2 2 * a 2 ⟨2, ⋯⟩ -
                                                        w * a 0 2 * a 0 ⟨2, ⋯⟩ * D 2 0 0 +
                                                      w * a 0 2 * a 1 ⟨2, ⋯⟩ * D 1 2 0 * (1 / 2) +
                                                    w * a 0 2 * a 1 ⟨2, ⋯⟩ * D 1 0 2 * (1 / 2) -
                                                  w * a 0 2 * a 1 ⟨2, ⋯⟩ * D 2 0 1 +
                                                w * a 0 2 * a 2 ⟨2, ⋯⟩ * D 2 2 0 * (1 / 2) +
                                              w * a 0 2 * a 2 ⟨2, ⋯⟩ * D 2 0 2 * (-1 / 2) +
                                            w * a 1 1 * D 0 1 1 * a 0 ⟨2, ⋯⟩ * (1 / 2) -
                                          w * a 1 1 * a 0 ⟨2, ⋯⟩ * D 1 1 0 +
                                        w * a 1 1 * a 1 ⟨2, ⋯⟩ * D 1 1 1 * (-1 / 2) -
                                      w * a 1 1 * a 2 ⟨2, ⋯⟩ * D 1 1 2 +
                                    w * a 1 1 * a 2 ⟨2, ⋯⟩ * D 2 1 1 * (1 / 2) +
                                  w * a 1 2 * D 0 2 1 * a 0 ⟨2, ⋯⟩ * (1 / 2) +
                                w * a 1 2 * D 0 1 2 * a 0 ⟨2, ⋯⟩ * (1 / 2) -
                              w * a 1 2 * a 0 ⟨2, ⋯⟩ * D 1 2 0 -
                            w * a 1 2 * a 0 ⟨2, ⋯⟩ * D 2 1 0 +
                          w * a 1 2 * a 1 ⟨2, ⋯⟩ * D 1 2 1 * (-1 / 2) +
                        w * a 1 2 * a 1 ⟨2, ⋯⟩ * D 1 1 2 * (1 / 2) -
                      w * a 1 2 * a 1 ⟨2, ⋯⟩ * D 2 1 1 -
                    w * a 1 2 * a 2 ⟨2, ⋯⟩ * D 1 2 2 +
                  w * a 1 2 * a 2 ⟨2, ⋯⟩ * D 2 2 1 * (1 / 2) +
                w * a 1 2 * a 2 ⟨2, ⋯⟩ * D 2 1 2 * (-1 / 2) +
              w * a 2 2 * D 0 2 2 * a 0 ⟨2, ⋯⟩ * (1 / 2) -
            w * a 2 2 * a 0 ⟨2, ⋯⟩ * D 2 2 0 +
          w * a 2 2 * a 1 ⟨2, ⋯⟩ * D 1 2 2 * (1 / 2) -
        w * a 2 2 * a 1 ⟨2, ⋯⟩ * D 2 2 1 +
      w * a 2 2 * a 2 ⟨2, ⋯⟩ * D 2 2 2 * (-1 / 2) =
    w * a 0 0 * D 0 0 0 * a ⟨2, ⋯⟩ 0 * (-1 / 2) - w * a 0 0 * D 0 0 1 * a ⟨2, ⋯⟩ 1 - w * a 0 0 * D 0 0 2 * a ⟨2, ⋯⟩ 2 +
                                                                                        w * a 0 0 * D 1 0 0 *
                                                                                            a ⟨2, ⋯⟩ 1 *
                                                                                          (1 / 2) +
                                                                                      w * a 0 0 * D 2 0 0 * a ⟨2, ⋯⟩ 2 *
                                                                                        (1 / 2) +
                                                                                    w * a 0 1 * D 0 1 0 * a ⟨2, ⋯⟩ 0 *
                                                                                      (-1 / 2) +
                                                                                  w * a 0 1 * D 0 0 1 * a ⟨2, ⋯⟩ 0 *
                                                                                    (1 / 2) -
                                                                                w * a 0 1 * D 0 1 1 * a ⟨2, ⋯⟩ 1 -
                                                                              w * a 0 1 * D 0 1 2 * a ⟨2, ⋯⟩ 2 -
                                                                            w * a 0 1 * D 1 0 0 * a ⟨2, ⋯⟩ 0 +
                                                                          w * a 0 1 * D 1 1 0 * a ⟨2, ⋯⟩ 1 * (1 / 2) +
                                                                        w * a 0 1 * D 1 0 1 * a ⟨2, ⋯⟩ 1 * (-1 / 2) -
                                                                      w * a 0 1 * D 1 0 2 * a ⟨2, ⋯⟩ 2 +
                                                                    w * a 0 1 * D 2 1 0 * a ⟨2, ⋯⟩ 2 * (1 / 2) +
                                                                  w * a 0 1 * D 2 0 1 * a ⟨2, ⋯⟩ 2 * (1 / 2) +
                                                                w * a 0 2 * D 0 2 0 * a ⟨2, ⋯⟩ 0 * (-1 / 2) -
                                                              w * a 0 2 * D 0 2 1 * a ⟨2, ⋯⟩ 1 +
                                                            w * a 0 2 * D 0 0 2 * a ⟨2, ⋯⟩ 0 * (1 / 2) -
                                                          w * a 0 2 * D 0 2 2 * a ⟨2, ⋯⟩ 2 +
                                                        w * a 0 2 * D 1 2 0 * a ⟨2, ⋯⟩ 1 * (1 / 2) +
                                                      w * a 0 2 * D 1 0 2 * a ⟨2, ⋯⟩ 1 * (1 / 2) -
                                                    w * a 0 2 * D 2 0 0 * a ⟨2, ⋯⟩ 0 +
                                                  w * a 0 2 * D 2 2 0 * a ⟨2, ⋯⟩ 2 * (1 / 2) -
                                                w * a 0 2 * D 2 0 1 * a ⟨2, ⋯⟩ 1 +
                                              w * a 0 2 * D 2 0 2 * a ⟨2, ⋯⟩ 2 * (-1 / 2) +
                                            w * a 1 1 * D 0 1 1 * a ⟨2, ⋯⟩ 0 * (1 / 2) -
                                          w * a 1 1 * D 1 1 0 * a ⟨2, ⋯⟩ 0 +
                                        w * a 1 1 * D 1 1 1 * a ⟨2, ⋯⟩ 1 * (-1 / 2) -
                                      w * a 1 1 * D 1 1 2 * a ⟨2, ⋯⟩ 2 +
                                    w * a 1 1 * D 2 1 1 * a ⟨2, ⋯⟩ 2 * (1 / 2) +
                                  w * a 1 2 * D 0 2 1 * a ⟨2, ⋯⟩ 0 * (1 / 2) +
                                w * a 1 2 * D 0 1 2 * a ⟨2, ⋯⟩ 0 * (1 / 2) -
                              w * a 1 2 * D 1 2 0 * a ⟨2, ⋯⟩ 0 +
                            w * a 1 2 * D 1 2 1 * a ⟨2, ⋯⟩ 1 * (-1 / 2) +
                          w * a 1 2 * D 1 1 2 * a ⟨2, ⋯⟩ 1 * (1 / 2) -
                        w * a 1 2 * D 1 2 2 * a ⟨2, ⋯⟩ 2 -
                      w * a 1 2 * D 2 1 0 * a ⟨2, ⋯⟩ 0 -
                    w * a 1 2 * D 2 1 1 * a ⟨2, ⋯⟩ 1 +
                  w * a 1 2 * D 2 2 1 * a ⟨2, ⋯⟩ 2 * (1 / 2) +
                w * a 1 2 * D 2 1 2 * a ⟨2, ⋯⟩ 2 * (-1 / 2) +
              w * a 2 2 * D 0 2 2 * a ⟨2, ⋯⟩ 0 * (1 / 2) +
            w * a 2 2 * D 1 2 2 * a ⟨2, ⋯⟩ 1 * (1 / 2) -
          w * a 2 2 * D 2 2 0 * a ⟨2, ⋯⟩ 0 -
        w * a 2 2 * D 2 2 1 * a ⟨2, ⋯⟩ 1 +
      w * a 2 2 * D 2 2 2 * a ⟨2, ⋯⟩ 2 * (-1 / 2)
```

### Command

```sh
rg -n 'fderiv_mul|HasFDerivAt.mul' .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean | head -12; sed -n '150,170p' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean; sed -n '45,64p' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean
```

Exit: 0

```text
198:theorem HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
205:theorem HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
257:theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
265:theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
294:theorem HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x) (b : 𝔸) :
299:theorem HasFDerivAt.mul_const (hc : HasFDerivAt c c' x) (d : 𝔸') :
333:theorem fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
337:theorem fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') :
569:theorem HasFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
589:theorem fderiv_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
593:  (HasFDerivAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivAt).fderiv
  refine ⟨isSelfAdjoint_sum s fun _ hi => h _ hi |>.1, fun y => ?_⟩
  simp [sum_apply, Finset.mul_sum, Finset.sum_mul, Finsupp.sum_finsetSum_comm,
    Finset.sum_nonneg fun _ hi => (h _ hi).2 _]

/-!
## Positive definite matrices
-/

/-- A matrix `M : Matrix n n R` is positive definite if it is Hermitian
and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ ⦃x : n →₀ R⦄, x ≠ 0 → 0 < x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj

namespace PosDef

theorem isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian :=
  hM.1

theorem posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef :=
  ⟨hM.1, fun x ↦ by obtain rfl | hx := eq_or_ne x 0 <;> simp [le_of_lt, hM.2, *]⟩


instance (A : Matrix n n α) [Decidable (Aᴴ = A)] : Decidable (IsHermitian A) :=
  inferInstanceAs <| Decidable (_ = _)

theorem IsHermitian.eq {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ = A := h

theorem isHermitian_iff_isSelfAdjoint {A : Matrix n n α} :
    A.IsHermitian ↔ IsSelfAdjoint A := Iff.rfl

protected alias ⟨IsHermitian.isSelfAdjoint, _root_.IsSelfAdjoint.isHermitian⟩ :=
  isHermitian_iff_isSelfAdjoint

theorem IsHermitian.ext {A : Matrix n n α} : (∀ i j, star (A j i) = A i j) → A.IsHermitian := by
  intro h; ext i j; exact h i j

theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j :=
  congr_fun (congr_fun h _) _

theorem IsHermitian.ext_iff {A : Matrix n n α} : A.IsHermitian ↔ ∀ i j, star (A j i) = A i j :=
  ⟨IsHermitian.apply, IsHermitian.ext⟩
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-8.lean
```

Exit: 0

```text
/tmp/stokes-global-evidence/dependencies-8.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.LineDeriv.Basic

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
theorem fderiv_chartWeight
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) :
    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
    (G := fun t : ℝ ↦ G (z + t • v))
    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hdet)
  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq

/-- Differentiating the inverse identity gives the full inverse-matrix derivative. -/
theorem deriv_matrix_inv_entry {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s ↦ A s i j) t)
    (hdet : (A t).det ≠ 0) (i j : Fin n) :
    deriv (fun s ↦ (A s)⁻¹ i j) t =
      -(∑ k, ∑ l, (A t)⁻¹ i k * deriv (fun s ↦ A s k l) t * (A t)⁻¹ l j) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
  let D : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ A s k l) t
  let Q : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ (A s)⁻¹ k l) t
  have hB (k l : Fin n) : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹ k l) t :=
    differentiableAt_matrix_inv_entry_of_entries hA hdet k l
  have hlocal : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 :=
    (differentiableAt_matrix_det_of_entries hA).continuousAt.eventually_ne hdet
  have hprod : Q * A t + B * D = 0 := by
    ext k l
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun m _ ↦ (hB k m).hasDerivAt.mul (hA m l).hasDerivAt)
    have heq : (fun s ↦ ∑ m, (A s)⁻¹ k m * A s m l) =ᶠ[𝓝 t]
        (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ) k l) := by
      filter_upwards [hlocal] with s hs
      exact congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T k l)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
    have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib, Q, B, D] using hzero
  have hab : A t * B = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hq : Q = -(B * D * B) := by
    have hh := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T * B) hprod
    dsimp only at hh
    rw [add_mul, Matrix.mul_assoc, hab, mul_one, zero_mul] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hentry := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T i j) hq
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, Q, B, D] at hentry
  rw [Finset.sum_comm] at hentry
  exact hentry

/-- The inverse Gram entries have the usual spatial derivative. -/
theorem fderiv_chartInverseMetric
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) (i j : Fin n) :
    fderiv ℝ (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z v =
      -(∑ k, ∑ l, (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
        fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y k l) z v *
        (inverseChartPullbackGramMatrixField g p z)⁻¹ l j) := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (k l : Fin n) : DifferentiableAt ℝ (fun y ↦ G y k l) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p k l z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hInv := (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hd := deriv_matrix_inv_entry (A := fun s : ℝ ↦ G (z + s • v)) (t := 0)
    (fun k l ↦ ((hG k l).hasFDerivAt.hasLineDerivAt v).differentiableAt)
    (by simpa only [zero_smul, add_zero] using hdet) i j
  rw [(hInv.hasFDerivAt.hasLineDerivAt v).deriv] at hd
  simp only [zero_smul, add_zero] at hd
  simpa only [((hG _ _).hasFDerivAt.hasLineDerivAt v).deriv] using hd

/-- The three-dimensional finite contraction behind the divergence identity. -/
theorem density_inverse_contraction_three
    (a : Matrix (Fin 3) (Fin 3) ℝ) (ha : a.IsSymm)
    (D : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : ℝ) (j : Fin 3) :
    (∑ k, (((1 / 2 : ℝ) * w * (∑ p, ∑ q, a p q * D k q p)) * a k j +
      w * (-(∑ p, ∑ q, a k p * D k p q * a q j)))) =
    w * (-(∑ k, ∑ l, a k l * ((1 / 2 : ℝ) *
      ∑ m, a j m * (D k l m + D l k m - D m k l)))) := by
  simp only [Fin.sum_univ_three]
  simp only [ha.apply j 0, ha.apply j 1, ha.apply j 2, show a 1 0 = a 0 1 from ha.apply 0 1,
      show a 2 0 = a 0 2 from ha.apply 0 2,
      show a 2 1 = a 1 2 from ha.apply 1 2]
  ring

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/compat.lean
```

Exit: 1

```text
/tmp/stokes-global-evidence/compat.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/stokes-global-evidence/compat.lean:250:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  fderiv ℝ (w * fun y => a y k j) z
in the target expression
  (fderiv ℝ (fun y => w y * a y k j) z) (EuclideanSpace.single k 1) =
    (1 / 2 * w z * ∑ l, ∑ m, a z l m * D k m l) * a z k j + w z * -∑ l, ∑ m, a z k l * D k l m * a z m j

M₃ : Type u
inst✝⁷ : TopologicalSpace M₃
inst✝⁶ : T2Space M₃
inst✝⁵ : CompactSpace M₃
inst✝⁴ : ConnectedSpace M₃
inst✝³ : MeasurableSpace M₃
inst✝² : BorelSpace M₃
inst✝¹ : ChartedSpace (ClosedSmoothModel 3) M₃
inst✝ : IsManifold (closedSmoothModelWithCorners 3) ∞ M₃
g : ClosedSmoothRiemannianMetric 3 M₃
p : M₃
G : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := inverseChartPullbackGramMatrixField g p
w : ClosedSmoothModel 3 → ℝ := fun z => ↑(rawHausdorffLebesgueScale 3) * VolumeDensity.chartVolumeDensity (G z)
a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z => (G z)⁻¹
Γ : ClosedSmoothModel 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun z j k l =>
    1 / 2 *
      ∑ m,
        a z j m *
          (coordinateDirectionalDerivative (fun y => G y l m) k z +
              coordinateDirectionalDerivative (fun y => G y k m) l z -
            coordinateDirectionalDerivative (fun y => G y k l) m z)
z : ClosedSmoothModel 3
hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target
j : Fin 3
hW : DifferentiableAt ℝ w z
hA : ∀ (k l : Fin 3), DifferentiableAt ℝ (fun y => a y k l) z
hsymm : (G z).IsSymm
D : Fin 3 → Fin 3 → Fin 3 → ℝ := fun k l m => (fderiv ℝ (fun y => G y l m) z) (EuclideanSpace.single k 1)
k : Fin 3
a✝ : k ∈ Finset.univ
⊢ (fderiv ℝ (fun y => w y * a y k j) z) (EuclideanSpace.single k 1) =
    (1 / 2 * w z * ∑ l, ∑ m, a z l m * D k m l) * a z k j + w z * -∑ l, ∑ m, a z k l * D k l m * a z m j
```

### Command

```sh
sed -n "244,270p" .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean
```

Exit: 0

```text
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (c * d) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

theorem fderiv_fun_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (fun y => a y * b y) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (a * b) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

theorem fderiv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (c * d) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

@[fun_prop]
theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Prove the three-dimensional density-Christoffel contraction"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients 865e199e] Prove the three-dimensional density-Christoffel contraction
 1 file changed, 14 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
rg -n '^theorem|^def|^noncomputable def' Poincare/Global/LeviCivitaTransport.lean | head -40; sed -n '210,285p' Poincare/Global/Laplacian.lean; sed -n '370,404p' Poincare/Global/Laplacian.lean; rg -n 'trace.*sum.*gram|trace.*basis|hessian.*(mfderiv|fderiv)|laplacian.*coordinate' Poincare/Global/MetricContraction*.lean Poincare/Global/*Laplacian*.lean | head -40
```

Exit: 0

```text
28:noncomputable def chartTransportedLeviCivitaSection
35:theorem chartTransportedLeviCivitaSection_apply
46:theorem chartTransportedLeviCivitaSection_apply_chart
73:theorem chartMetric_chartTransportedLeviCivitaSection
111:theorem chartTransportedLeviCivitaSection_mlieBracket_apply_chart
157:theorem chartTransportedLeviCivitaSection_mdiffAt_apply_chart
197:noncomputable def chartTransportedLeviCivitaModelValue
213:theorem chartTransportedLeviCivitaModelValue_apply
235:noncomputable def chartTransportedLeviCivitaValueAt
250:theorem chartTransportedLeviCivitaValueAt_apply
269:theorem chartTransportedLeviCivita_mem_target
276:theorem chartTransportedLeviCivita_left_inv
283:theorem chartTransportedLeviCivita_direction_roundtrip
299:theorem chartTransported_torsionFreeAt
385:theorem chartTransported_metricCompatibleAt
576:theorem chartTransportedLeviCivitaValueAt_eq_closed_of_isLeviCivitaAt
625:theorem chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
`df`, and the pulled-back field agrees locally with the intrinsic gradient by
the defining metric-duality property.
-/
theorem mdifferentiableAt_gradient (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
  haveI : ModelWithCorners.Boundaryless I := by infer_instance
  let G₀ : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v := by
    intro v hv
    change 0 < ((innerSL ℝ) v) v
    rw [innerSL_apply_apply]
    exact (real_inner_self_pos).2 hv
  obtain ⟨χ, hχ, hχ0, hχ1, hχsupp, hχone, _hχcanonical⟩ :=
    @CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x
  have hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x).symm)
        (Set.range I) z).IsInvertible := by
    intro z hz
    exact isInvertible_mfderivWithin_extChartAt_symm
      (hχsupp (subset_tsupport χ (Function.mem_support.mpr hz)))
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  let Ghat : E → E →L[ℝ] E →L[ℝ] ℝ :=
    CovariantDerivative.blendedChartMetric χ G₀ g.inner x
  have hGhat : ContDiff ℝ 2 Ghat := by
    simpa [Ghat] using
      CovariantDerivative.contDiff_blendedChartMetric χ G₀ g.inner x
        htwo_add_one_le_top hχ hχsupp hg2
  have hGhatInv : ∀ z : E, (Ghat z).IsInvertible := by
    intro z
    exact CovariantDerivative.metric_isInvertible Ghat
      (CovariantDerivative.chartBilin χ G₀ g.inner x z)
      (CovariantDerivative.chartBilin_nondegenerate χ G₀ hG₀pos g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x hχ0 hχ1 hsupp z)
      (by intro v w; rfl)
  let F : E → ℝ := f ∘ (extChartAt I x).symm
  have hF : ContDiffAt ℝ 2 F (extChartAt I x x) := by
    have h := (contMDiffAt_iff.mp hf).2
    rw [ModelWithCorners.range_eq_univ I, contDiffWithinAt_univ] at h
    have heq :
        (extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ (extChartAt I x).symm =
          f ∘ (extChartAt I x).symm := by
      funext z
      simp
    rw [heq] at h
    simpa [F] using h
  let V : ∀ z : E, TangentSpace 𝓘(ℝ, E) z :=
    fun z ↦ RicciFlow.RicciFlow.coordGradient Ghat F z
  have hVdiff : DifferentiableAt ℝ V (extChartAt I x x) := by
    have hInvDiff :
        DifferentiableAt ℝ (fun z : E => (Ghat z).inverse)
          (extChartAt I x x) :=
      (((hGhatInv (extChartAt I x x)).contDiffAt_map_inverse (n := 1)).differentiableAt
          one_ne_zero).comp (extChartAt I x x)
        ((hGhat.contDiffAt).differentiableAt (by norm_num))
    have hdfd : DifferentiableAt ℝ (fderiv ℝ F) (extChartAt I x x) :=
      ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    simpa [V, RicciFlow.RicciFlow.coordGradient] using hInvDiff.clm_apply hdfd
  have hVmdiff :
      MDifferentiableAt 𝓘(ℝ, E) ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (T% V)
        (extChartAt I x x) :=
                g.inner y (W y) w
                    = CovariantDerivative.chartMetric g.inner x
                        (extChartAt I x y) (V (extChartAt I x y))
                        ((mfderiv I 𝓘(ℝ, E)
                          ((extChartAt I x : PartialEquiv M E) : M → E) y) w) := hmetric
                _ = Ghat (extChartAt I x y) (V (extChartAt I x y))
                        ((mfderiv I 𝓘(ℝ, E)
                          ((extChartAt I x : PartialEquiv M E) : M → E) y) w) := by
                    rw [hGchart]
                _ = fderiv ℝ F (extChartAt I x y)
                        ((mfderiv I 𝓘(ℝ, E)
                          ((extChartAt I x : PartialEquiv M E) : M → E) y) w) := hmodel
                _ = extDerivFun f y w := by
                    symm
                    simpa [F] using
                      extDerivFun_apply_fixed_chart hy hfy w
            calc
              g.inner y (g.gradient f y - W y) w
                  = g.inner y (g.gradient f y) w - g.inner y (W y) w := by
                    simp only [map_sub, ContinuousLinearMap.sub_apply]
              _ = 0 := by rw [hleft, hright, sub_self])
      simpa using (sub_eq_zero.mp hzero)
    rw [hgrad_eq]
  exact hW.congr_of_eventuallyEq hev

/--
The covariant Hessian of a scalar function at `x`:
`Hess f(v,w) = g(∇_v grad f, w)`.
-/
noncomputable def hessianAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) (v w : TM x) : ℝ :=
  g.inner x (g.leviCivita (g.gradient f) x v) w

theorem hessianAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
zsh:1: no matches found: Poincare/Global/MetricContraction*.lean
```

### Command

```sh
rg -n '(hessian|laplacian|coordLaplacian|coordHessian)' Poincare/ModelLaplacian*.lean | head -65; sed -n '615,671p' Poincare/Global/LeviCivitaTransport.lean; rg -n 'chartMetric.*Gram|Gram.*chartMetric' Poincare/Global/HausdorffInverseChartGramContinuity.lean Poincare/Global/HamiltonChartDensityLocalDomination.lean Poincare/Global/HausdorffFrozenInverseChartAreaFormula.lean
```

Exit: 1

```text
Poincare/ModelLaplacianRootAliases.lean:60:    b_hessianOperator
Poincare/ModelLaplacianRootAliases.lean:96:    gaussian_laplacian
Poincare/ModelLaplacianRootAliases.lean:97:    gaussian_soliton_hessian
Poincare/ModelLaplacianRootAliases.lean:106:    hessianNormSq
Poincare/ModelLaplacianRootAliases.lean:107:    hessianNormSq_nonneg
Poincare/ModelLaplacianRootAliases.lean:108:    hessianOperator
Poincare/ModelLaplacianRootAliases.lean:109:    hessian_nonneg_of_isLocalMin
Poincare/ModelLaplacianRootAliases.lean:127:    modelLaplacian_eq_trace_hessianOperator
Poincare/ModelLaplacianRootAliases.lean:372:    bochner_equality_iff_hessian_vanishes
Poincare/ModelLaplacianRootAliases.lean:476:    coordCovariantHessNormSq_eq_zero_iff_hessian_flat
Poincare/ModelLaplacianRootAliases.lean:677:    curvedLap_tensorMetricTrace_hessian_form
Poincare/ModelLaplacianRootAliases.lean:679:    curvedLaplacian_const_eq_flat_hessian_trace
Poincare/ModelLaplacianRootAliases.lean:693:    curvedLaplacian_eq_raised_hessian_sum
Poincare/ModelLaplacianRootAliases.lean:726:    deltaGammaContractionDeriv_eq_half_hessian
Poincare/ModelLaplacianRootAliases.lean:895:    fderiv_hessianOperator_apply
Poincare/ModelLaplacianRootAliases.lean:898:    fderiv_metricGradient_eq_hessianOperator
Poincare/ModelLaplacianRootAliases.lean:955:    hessianNormSq_eq_orthoBasis_sum
Poincare/ModelLaplacianRootAliases.lean:956:    hessianOperator_selfAdjoint
Poincare/ModelLaplacianRootAliases.lean:957:    hessian_eq_zero_of_hessianNormSq_eq_zero
Poincare/ModelLaplacianRootAliases.lean:982:    laplacian_sq_le_finrank_mul_hessianNormSq
Poincare/ModelLaplacianRootAliases.lean:1059:    ricciDeriv_eq_div_sub_half_hessian
Poincare/ModelLaplacianRootAliases.lean:1063:    ricciDeriv_fderiv_hessian_form
Poincare/ModelLaplacianRootAliases.lean:1212:    sum_hessian_trace_raise_swap
Poincare/ModelLaplacianRootAliases.lean:1219:    sum_sum_covTensor2SndDeriv_laplacian_trace
Poincare/ModelLaplacianRootAliases.lean:1271:    traceless_hessian_normSq_nonneg
Poincare/ModelLaplacian.lean:278:    (fun v ↦ hessian_nonneg_of_isLocalMin hf hmin v)
Poincare/ModelLaplacian.lean:1872:theorem gaussian_laplacian (b : LinearMap.BilinForm ℝ E)
Poincare/ModelLaplacian.lean:1906:theorem gaussian_soliton_hessian (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
Poincare/ModelLaplacian.lean:2029:    gaussian_soliton_hessian G₀ b₀ hb₀ hbs hτ x v w]
Poincare/ModelLaplacian.lean:3066:noncomputable def hessianOperator (b : LinearMap.BilinForm ℝ E)
Poincare/ModelLaplacian.lean:3073:theorem modelLaplacian_eq_trace_hessianOperator
Poincare/ModelLaplacian.lean:3077:      LinearMap.trace ℝ E (hessianOperator b hb f x) := rfl
Poincare/ModelLaplacian.lean:3081:noncomputable def hessianNormSq (b : LinearMap.BilinForm ℝ E)
Poincare/ModelLaplacian.lean:3084:    (hessianOperator b hb f x ∘ₗ hessianOperator b hb f x)
Poincare/ModelLaplacian.lean:3097:theorem b_hessianOperator (b : LinearMap.BilinForm ℝ E)
Poincare/ModelLaplacian.lean:3099:    b (hessianOperator b hb f x v) w =
Poincare/ModelLaplacian.lean:3114:theorem hessianNormSq_nonneg (b : LinearMap.BilinForm ℝ E)
Poincare/ModelLaplacian.lean:3118:    0 ≤ hessianNormSq b hb f x := by
Poincare/ModelLaplacian.lean:3121:  set A := hessianOperator b hb f x with hA
Poincare/ModelLaplacian.lean:3125:    rw [b_hessianOperator]
Poincare/ModelLaplacian.lean:3128:    rw [hsy, b_hessianOperator]
Poincare/ModelLaplacian.lean:3130:  unfold hessianNormSq
Poincare/ModelLaplacian.lean:7244:theorem curvedLaplacian_eq_raised_hessian_sum
Poincare/ModelLaplacian.lean:13840:theorem curvedLap_tensorMetricTrace_hessian_form
Poincare/ModelLaplacian.lean:14456:theorem sum_sum_covTensor2SndDeriv_laplacian_trace
Poincare/ModelLaplacian.lean:14497:theorem sum_hessian_trace_raise_swap
Poincare/ModelLaplacian.lean:14559:  rw [sum_sum_covTensor2SndDeriv_laplacian_trace hGd hGsymm hinv hHd hH2 hΓd hHsymm,
Poincare/ModelLaplacian.lean:14560:    Finset.sum_sub_distrib, sum_hessian_trace_raise_swap hGsymm hinv hTr2,
Poincare/ModelLaplacian.lean:14561:    curvedLap_tensorMetricTrace_hessian_form hGsymm hinv, Finset.sum_sub_distrib]
Poincare/ModelLaplacian.lean:16637:theorem deltaGammaContractionDeriv_eq_half_hessian
Poincare/ModelLaplacian.lean:16672:theorem ricciDeriv_eq_div_sub_half_hessian
Poincare/ModelLaplacian.lean:16690:    deltaGammaContractionDeriv_eq_half_hessian hGd hGsymm hinv hHd hHsymm hVd
Poincare/ModelLaplacian.lean:16708:theorem ricciDeriv_fderiv_hessian_form
Poincare/ModelLaplacian.lean:16739:  rw [ricciDeriv_eq_div_sub_half_hessian hGd hGsymm hinv hHd hHsymm hVd hTr2
Poincare/ModelLaplacian.lean:16754:`deltaGammaContractionDeriv_eq_half_hessian` via `covTensor1Deriv_fderiv_eq_covariantHessian`.
Poincare/ModelLaplacian.lean:16771:  rw [deltaGammaContractionDeriv_eq_half_hessian hGd hGsymm hinv hHd hHsymm hVd
Poincare/ModelLaplacian.lean:26390:spectral input behind `hessianNormSq_nonneg` (real eigenvalues / orthogonal diagonalizability of the
Poincare/ModelLaplacian.lean:26392:theorem hessianOperator_selfAdjoint (b : LinearMap.BilinForm ℝ E)
Poincare/ModelLaplacian.lean:26395:    b (hessianOperator b hb f x v) w = b v (hessianOperator b hb f x w) := by
Poincare/ModelLaplacian.lean:26396:  rw [b_hessianOperator]
Poincare/ModelLaplacian.lean:26397:  have hsy := hbs.eq v (hessianOperator b hb f x w)
Poincare/ModelLaplacian.lean:26399:  rw [hsy, b_hessianOperator]
Poincare/ModelLaplacian.lean:26412:`fderiv (∇f) x v = hessianOperator b hb f x v`. In the flat (fixed-form) model the gradient is a fixed
Poincare/ModelLaplacian.lean:26415:*analytic* gradient-of-gradient to the *algebraic* Hessian operator (`hessianOperator`), the missing
Poincare/ModelLaplacian.lean:26418:theorem fderiv_metricGradient_eq_hessianOperator
    (fun u hu => LeviCivitaExistence.metric_nondegenerate g y u hu)
    hcT hcClosed htT htClosed
    (by simpa [MDiffAtTangentField] using hσ)
  exact (htransport v).symm.trans (congrArg (fun L => L v) huniq)

/--
On a chart sub-neighborhood where the blending cutoff is identically `1`, the
transported chart Levi-Civita value agrees with the closed smooth
Levi-Civita connection.
-/
theorem chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
    (g : ClosedSmoothRiemannianMetric n M)
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hbl : Differentiable ℝ (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀))
    (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    {σ : Π y : M, TM y} {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone : ∀ᶠ z' in 𝓝 (extChartAt I x₀ y), χ z' = 1)
    (hσ : MDiffAtTangentField σ y)
    (v : TM y) :
    CovariantDerivative.chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp σ hy v =
      (LeviCivitaExistence.closedLeviCivitaConnection g) σ y v := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : ModelWithCorners.Boundaryless (closedSmoothModelWithCorners n) := by
    infer_instance
  let z : E := extChartAt I x₀ y
  let D : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TM y :=
    mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (Set.range I) z
  let covC :=
    CovariantDerivative.chartLeviCivita χ G₀ hG₀pos g.inner
      (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp
  let covT : (Π y : M, TM y) → TM y →L[ℝ] TM y :=
    fun X =>
      let Xc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
        CovariantDerivative.chartTransportedLeviCivitaSection x₀ X
      D.comp ((covC Xc z).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y))
  let covClosed : (Π y : M, TM y) → TM y →L[ℝ] TM y :=
    fun X => (LeviCivitaExistence.closedLeviCivitaConnection g) X y
  have hcompatT :
      ∀ {Y Z : Π y : M, TM y},
        MDiffAtTangentField Y y → MDiffAtTangentField Z y →
          ∀ v : TM y,
            extDerivFun (fun p => g.inner p (Y p) (Z p)) y v =
              g.inner y (covT Y v) (Z y) + g.inner y (Y y) (covT Z v) := by
    intro Y Z hY hZ w
    have hYZ :
        MDifferentiableAt I 𝓘(ℝ) (fun p : M => g.inner p (Y p) (Z p)) y := by
      exact LeviCivitaExistence.metric_pairing_mdiffAt g hY hZ
    simpa [covT, covC, D, z, CovariantDerivative.chartTransportedLeviCivitaValueAt,
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-9.lean
```

Exit: 0

```text
/tmp/stokes-global-evidence/dependencies-9.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.LineDeriv.Basic

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
theorem fderiv_chartWeight
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) :
    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
    (G := fun t : ℝ ↦ G (z + t • v))
    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hdet)
  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq

/-- Differentiating the inverse identity gives the full inverse-matrix derivative. -/
theorem deriv_matrix_inv_entry {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s ↦ A s i j) t)
    (hdet : (A t).det ≠ 0) (i j : Fin n) :
    deriv (fun s ↦ (A s)⁻¹ i j) t =
      -(∑ k, ∑ l, (A t)⁻¹ i k * deriv (fun s ↦ A s k l) t * (A t)⁻¹ l j) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
  let D : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ A s k l) t
  let Q : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ (A s)⁻¹ k l) t
  have hB (k l : Fin n) : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹ k l) t :=
    differentiableAt_matrix_inv_entry_of_entries hA hdet k l
  have hlocal : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 :=
    (differentiableAt_matrix_det_of_entries hA).continuousAt.eventually_ne hdet
  have hprod : Q * A t + B * D = 0 := by
    ext k l
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun m _ ↦ (hB k m).hasDerivAt.mul (hA m l).hasDerivAt)
    have heq : (fun s ↦ ∑ m, (A s)⁻¹ k m * A s m l) =ᶠ[𝓝 t]
        (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ) k l) := by
      filter_upwards [hlocal] with s hs
      exact congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T k l)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
    have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib, Q, B, D] using hzero
  have hab : A t * B = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hq : Q = -(B * D * B) := by
    have hh := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T * B) hprod
    dsimp only at hh
    rw [add_mul, Matrix.mul_assoc, hab, mul_one, zero_mul] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hentry := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T i j) hq
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, Q, B, D] at hentry
  rw [Finset.sum_comm] at hentry
  exact hentry

/-- The inverse Gram entries have the usual spatial derivative. -/
theorem fderiv_chartInverseMetric
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) (i j : Fin n) :
    fderiv ℝ (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z v =
      -(∑ k, ∑ l, (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
        fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y k l) z v *
        (inverseChartPullbackGramMatrixField g p z)⁻¹ l j) := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (k l : Fin n) : DifferentiableAt ℝ (fun y ↦ G y k l) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p k l z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hInv := (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hd := deriv_matrix_inv_entry (A := fun s : ℝ ↦ G (z + s • v)) (t := 0)
    (fun k l ↦ ((hG k l).hasFDerivAt.hasLineDerivAt v).differentiableAt)
    (by simpa only [zero_smul, add_zero] using hdet) i j
  rw [(hInv.hasFDerivAt.hasLineDerivAt v).deriv] at hd
  simp only [zero_smul, add_zero] at hd
  simpa only [((hG _ _).hasFDerivAt.hasLineDerivAt v).deriv] using hd

/-- The three-dimensional finite contraction behind the divergence identity. -/
theorem density_inverse_contraction_three
    (a : Matrix (Fin 3) (Fin 3) ℝ) (ha : a.IsSymm)
    (D : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : ℝ) (j : Fin 3) :
    (∑ k, (((1 / 2 : ℝ) * w * (∑ p, ∑ q, a p q * D k q p)) * a k j +
      w * (-(∑ p, ∑ q, a k p * D k p q * a q j)))) =
    w * (-(∑ k, ∑ l, a k l * ((1 / 2 : ℝ) *
      ∑ m, a j m * (D k l m + D l k m - D m k l)))) := by
  simp only [Fin.sum_univ_three]
  simp only [ha.apply j 0, ha.apply j 1, ha.apply j 2, show a 1 0 = a 0 1 from ha.apply 0 1,
      show a 2 0 = a 0 2 from ha.apply 0 2,
      show a 2 1 = a 1 2 from ha.apply 1 2]
  ring

variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
  [ChartedSpace (ClosedSmoothModel 3) M₃]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]

/-- The genuine density and inverse metric satisfy the chart divergence identity. -/
theorem density_inverseMetric_compatibility
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃) :
    let G := inverseChartPullbackGramMatrixField g p
    let w := fun z ↦ (rawHausdorffLebesgueScale 3 : ℝ) * VolumeDensity.chartVolumeDensity (G z)
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z ↦ (G z)⁻¹
    let Γ := fun z j k l ↦ (1 / 2 : ℝ) * ∑ m, a z j m *
      (coordinateDirectionalDerivative (fun y ↦ G y l m) k z +
       coordinateDirectionalDerivative (fun y ↦ G y k m) l z -
       coordinateDirectionalDerivative (fun y ↦ G y k l) m z)
    ∀ z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target, ∀ j : Fin 3,
      (∑ k, fderiv ℝ (fun y ↦ w y * a y k j) z (EuclideanSpace.single k (1 : ℝ))) =
      w z * (-(∑ k, ∑ l, a z k l * Γ z j k l)) := by
  intro G w a Γ z hz j
  have hW : DifferentiableAt ℝ w z :=
    (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hA (k l : Fin 3) : DifferentiableAt ℝ (fun y ↦ a y k l) z :=
    (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p k l) z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hsymm : (G z).IsSymm := by
    have hp := (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).isHermitian
    rw [inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩] at hp
    exact Matrix.IsSymm.ext (fun k l ↦ by simpa using hp.apply k l)
  let D := fun k l m ↦ fderiv ℝ (fun y ↦ G y l m) z (EuclideanSpace.single k (1 : ℝ))
  calc
    _ = ∑ k, (((1 / 2 : ℝ) * w z * (∑ l, ∑ m, a z l m * D k m l)) * a z k j +
        w z * (-(∑ l, ∑ m, a z k l * D k l m * a z m j))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fderiv_fun_mul hW (hA k j)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_chartWeight g p hz, fderiv_chartInverseMetric g p hz]
      dsimp only [w, a, G, D]
      ring
    _ = _ := density_inverse_contraction_three (a z) hsymm.inv D (w z) j

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Prove the genuine chart density divergence identity in dimension three"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients f6c39b46] Prove the genuine chart density divergence identity in dimension three
 1 file changed, 42 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/finite.lean
```

Exit: 0

```text
/tmp/stokes-global-evidence/finite.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
rg -n 'theorem.*Event.*fderiv_eq|theorem.*fderiv_eq' .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean | head -12; rg -n 'exists_blending_cutoff|exists_global_chart_metric|contDiff_blendedChartMetric_scalar' Poincare/ChartTransport.lean; rg -n '^import|christoffel_eq_connection|koszul_apply' Poincare/Global/DeTurckPrincipalIdentity.lean | head -12
```

Exit: 0

```text
415:theorem fderiv_eq
353:theorem exists_blending_cutoff [I.Boundaryless] (x₀ : M) :
386:theorem exists_global_chart_metric [I.Boundaryless]
398:    exists_blending_cutoff (I := I) x₀
597:theorem contDiff_blendedChartMetric_scalar
653:  exact contDiff_blendedChartMetric_scalar χ G₀ g x₀ hm hχ htsupp hg v w
766:/-- Theorem contract for `contDiff_blendedChartMetric_scalar`. -/
767:theorem contDiff_blendedChartMetric_scalar_eq :
768:    @contDiff_blendedChartMetric_scalar = @contDiff_blendedChartMetric_scalar :=
860:/-- Theorem contract for `exists_blending_cutoff`. -/
861:theorem exists_blending_cutoff_eq :
862:    @CovariantDerivative.exists_blending_cutoff = @CovariantDerivative.exists_blending_cutoff :=
865:/-- Theorem contract for `exists_global_chart_metric`. -/
866:theorem exists_global_chart_metric_eq :
867:    @CovariantDerivative.exists_global_chart_metric = @CovariantDerivative.exists_global_chart_metric :=
1:import Poincare.Global.DeTurckPrincipalSecondJet
24:theorem koszul_apply (J : Jet1) (u v q : E) :
202:      simp only [hraise, koszul_apply, lieTensor_apply]
237:      simp only [koszul_apply]
267:          simp only [koszul_apply, map_add, ContinuousLinearMap.add_apply]
275:          simp only [koszul_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
283:          simp only [koszul_apply, map_add, ContinuousLinearMap.add_apply]
291:          simp only [koszul_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
384:theorem christoffel_eq_connection
523:    christoffel_eq_connection g anchor z hcut]
545:    anchorChartChristoffelFieldFlow, hval, christoffel_eq_connection g anchor z hcut]
583:    christoffel_eq_connection g anchor z hcut,
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-10.lean
```

Exit: 0

```text
/tmp/stokes-global-evidence/dependencies-10.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility_of_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.LineDeriv.Basic

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
theorem fderiv_chartWeight
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) :
    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
    (G := fun t : ℝ ↦ G (z + t • v))
    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hdet)
  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq

/-- Differentiating the inverse identity gives the full inverse-matrix derivative. -/
theorem deriv_matrix_inv_entry {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s ↦ A s i j) t)
    (hdet : (A t).det ≠ 0) (i j : Fin n) :
    deriv (fun s ↦ (A s)⁻¹ i j) t =
      -(∑ k, ∑ l, (A t)⁻¹ i k * deriv (fun s ↦ A s k l) t * (A t)⁻¹ l j) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
  let D : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ A s k l) t
  let Q : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ (A s)⁻¹ k l) t
  have hB (k l : Fin n) : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹ k l) t :=
    differentiableAt_matrix_inv_entry_of_entries hA hdet k l
  have hlocal : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 :=
    (differentiableAt_matrix_det_of_entries hA).continuousAt.eventually_ne hdet
  have hprod : Q * A t + B * D = 0 := by
    ext k l
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun m _ ↦ (hB k m).hasDerivAt.mul (hA m l).hasDerivAt)
    have heq : (fun s ↦ ∑ m, (A s)⁻¹ k m * A s m l) =ᶠ[𝓝 t]
        (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ) k l) := by
      filter_upwards [hlocal] with s hs
      exact congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T k l)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
    have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib, Q, B, D] using hzero
  have hab : A t * B = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hq : Q = -(B * D * B) := by
    have hh := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T * B) hprod
    dsimp only at hh
    rw [add_mul, Matrix.mul_assoc, hab, mul_one, zero_mul] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hentry := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T i j) hq
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, Q, B, D] at hentry
  rw [Finset.sum_comm] at hentry
  exact hentry

/-- The inverse Gram entries have the usual spatial derivative. -/
theorem fderiv_chartInverseMetric
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) (i j : Fin n) :
    fderiv ℝ (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z v =
      -(∑ k, ∑ l, (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
        fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y k l) z v *
        (inverseChartPullbackGramMatrixField g p z)⁻¹ l j) := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (k l : Fin n) : DifferentiableAt ℝ (fun y ↦ G y k l) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p k l z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hInv := (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hd := deriv_matrix_inv_entry (A := fun s : ℝ ↦ G (z + s • v)) (t := 0)
    (fun k l ↦ ((hG k l).hasFDerivAt.hasLineDerivAt v).differentiableAt)
    (by simpa only [zero_smul, add_zero] using hdet) i j
  rw [(hInv.hasFDerivAt.hasLineDerivAt v).deriv] at hd
  simp only [zero_smul, add_zero] at hd
  simpa only [((hG _ _).hasFDerivAt.hasLineDerivAt v).deriv] using hd

/-- The three-dimensional finite contraction behind the divergence identity. -/
theorem density_inverse_contraction_three
    (a : Matrix (Fin 3) (Fin 3) ℝ) (ha : a.IsSymm)
    (D : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : ℝ) (j : Fin 3) :
    (∑ k, (((1 / 2 : ℝ) * w * (∑ p, ∑ q, a p q * D k q p)) * a k j +
      w * (-(∑ p, ∑ q, a k p * D k p q * a q j)))) =
    w * (-(∑ k, ∑ l, a k l * ((1 / 2 : ℝ) *
      ∑ m, a j m * (D k l m + D l k m - D m k l)))) := by
  simp only [Fin.sum_univ_three]
  simp only [ha.apply j 0, ha.apply j 1, ha.apply j 2, show a 1 0 = a 0 1 from ha.apply 0 1,
      show a 2 0 = a 0 2 from ha.apply 0 2,
      show a 2 1 = a 1 2 from ha.apply 1 2]
  ring

variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
  [ChartedSpace (ClosedSmoothModel 3) M₃]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]

/-- The genuine density and inverse metric satisfy the chart divergence identity. -/
theorem density_inverseMetric_compatibility
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃) :
    let G := inverseChartPullbackGramMatrixField g p
    let w := fun z ↦ (rawHausdorffLebesgueScale 3 : ℝ) * VolumeDensity.chartVolumeDensity (G z)
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z ↦ (G z)⁻¹
    let Γ := fun z j k l ↦ (1 / 2 : ℝ) * ∑ m, a z j m *
      (coordinateDirectionalDerivative (fun y ↦ G y l m) k z +
       coordinateDirectionalDerivative (fun y ↦ G y k m) l z -
       coordinateDirectionalDerivative (fun y ↦ G y k l) m z)
    ∀ z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target, ∀ j : Fin 3,
      (∑ k, fderiv ℝ (fun y ↦ w y * a y k j) z (EuclideanSpace.single k (1 : ℝ))) =
      w z * (-(∑ k, ∑ l, a z k l * Γ z j k l)) := by
  intro G w a Γ z hz j
  have hW : DifferentiableAt ℝ w z :=
    (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hA (k l : Fin 3) : DifferentiableAt ℝ (fun y ↦ a y k l) z :=
    (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p k l) z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hsymm : (G z).IsSymm := by
    have hp := (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).isHermitian
    rw [inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩] at hp
    exact Matrix.IsSymm.ext (fun k l ↦ by simpa using hp.apply k l)
  let D := fun k l m ↦ fderiv ℝ (fun y ↦ G y l m) z (EuclideanSpace.single k (1 : ℝ))
  calc
    _ = ∑ k, (((1 / 2 : ℝ) * w z * (∑ l, ∑ m, a z l m * D k m l)) * a z k j +
        w z * (-(∑ l, ∑ m, a z k l * D k l m * a z m j))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fderiv_fun_mul hW (hA k j)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_chartWeight g p hz, fderiv_chartInverseMetric g p hz]
      dsimp only [w, a, G, D]
      ring
    _ = _ := density_inverse_contraction_three (a z) hsymm.inv D (w z) j

/-- Global coefficient extensions inherit compatibility wherever they agree locally. -/
theorem density_inverseMetric_compatibility_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
    (w' : ClosedSmoothModel 3 → ℝ)
    (a' : ClosedSmoothModel 3 → Fin 3 → Fin 3 → ℝ) :
    let G := inverseChartPullbackGramMatrixField g p
    let w := fun z ↦ (rawHausdorffLebesgueScale 3 : ℝ) * VolumeDensity.chartVolumeDensity (G z)
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z ↦ (G z)⁻¹
    let Γ := fun z j k l ↦ (1 / 2 : ℝ) * ∑ m, a z j m *
      (coordinateDirectionalDerivative (fun y ↦ G y l m) k z +
       coordinateDirectionalDerivative (fun y ↦ G y k m) l z -
       coordinateDirectionalDerivative (fun y ↦ G y k l) m z)
    ∀ z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target,
      w' =ᶠ[𝓝 z] w → a' =ᶠ[𝓝 z] a → ∀ j : Fin 3,
      (∑ k, fderiv ℝ (fun y ↦ w' y * a' y k j) z (EuclideanSpace.single k (1 : ℝ))) =
      w' z * (-(∑ k, ∑ l, a' z k l * Γ z j k l)) := by
  intro G w a Γ z hz hw ha j
  have hprod (k : Fin 3) :
      (fun y ↦ w' y * a' y k j) =ᶠ[𝓝 z] (fun y ↦ w y * a y k j) := by
    filter_upwards [hw, ha] with y hy hya
    rw [hy, hya]
  simp_rw [(hprod _).fderiv_eq]
  rw [hw.self_of_nhds, ha.self_of_nhds]
  exact density_inverseMetric_compatibility g p z hz j

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility_of_eventuallyEq
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Transfer the divergence identity to locally agreeing global coefficients"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients 3c3b7cd0] Transfer the divergence identity to locally agreeing global coefficients
 1 file changed, 25 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/resisting.lean
```

Exit: 1

```text
/tmp/stokes-global-evidence/resisting.lean:90:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/stokes-global-evidence/resisting.lean:322:75: error: unsolved goals
n : ℕ
M : Type u
inst✝¹⁵ : TopologicalSpace M
inst✝¹⁴ : T2Space M
inst✝¹³ : CompactSpace M
inst✝¹² : ConnectedSpace M
inst✝¹¹ : MeasurableSpace M
inst✝¹⁰ : BorelSpace M
inst✝⁹ : ChartedSpace E M
inst✝⁸ : IsManifold I ∞ M
M₃ : Type u
inst✝⁷ : TopologicalSpace M₃
inst✝⁶ : T2Space M₃
inst✝⁵ : CompactSpace M₃
inst✝⁴ : ConnectedSpace M₃
inst✝³ : MeasurableSpace M₃
inst✝² : BorelSpace M₃
inst✝¹ : ChartedSpace (ClosedSmoothModel 3) M₃
inst✝ : IsManifold (closedSmoothModelWithCorners 3) ∞ M₃
g : ClosedSmoothRiemannianMetric 3 M₃
p : M₃
V : Set M₃
hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
φ : M₃ → ℝ
hφ : tsupport φ ⊆ V
hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) 2 φ
z : ↑(extChartAt (closedSmoothModelWithCorners 3) p).target
hz : ↑z ∈ ↑(extChartAt (closedSmoothModelWithCorners 3) p) '' V
G : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := inverseChartPullbackGramMatrixField g p
a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y => (G y)⁻¹
Γ : ClosedSmoothModel 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun y j k l =>
    1 / 2 *
      ∑ m,
        a y j m *
          (coordinateDirectionalDerivative (fun q => G q l m) k y +
              coordinateDirectionalDerivative (fun q => G q k m) l y -
            coordinateDirectionalDerivative (fun q => G q k l) m y)
hsource : tsupport φ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
hu : ContDiff ℝ 2 (ClosedLaplacianStokesProducer.coordinateScalar p φ)
hcompat :
  ∀ (j : Fin 3),
    ∑ k,
        (fderiv ℝ
            (fun y =>
              (fun z =>
                    ↑(rawHausdorffLebesgueScale 3) *
                      VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
                  y *
                (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) y k j)
            ↑z)
          (EuclideanSpace.single k 1) =
      (fun z =>
            ↑(rawHausdorffLebesgueScale 3) *
              VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
          ↑z *
        -∑ k,
            ∑ l,
              (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) (↑z) k l *
                (fun z j k l =>
                    1 / 2 *
                      ∑ m,
                        (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) z j m *
                          (coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y l m) k
                                z +
                              coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k m) l
                                z -
                            coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k l) m
                              z))
                  (↑z) j k l
⊢ (LinearMap.trace ℝ (TangentSpace (closedSmoothModelWithCorners 3) (inverseExtendedChartParametrization p z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization p z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ ↑(g.hessianContinuousAt φ (inverseExtendedChartParametrization p z))) =
    christoffelCoordinateLaplacian a Γ (ClosedLaplacianStokesProducer.coordinateScalar p φ) ↑z
n : ℕ
M : Type u
inst✝¹⁵ : TopologicalSpace M
inst✝¹⁴ : T2Space M
inst✝¹³ : CompactSpace M
inst✝¹² : ConnectedSpace M
inst✝¹¹ : MeasurableSpace M
inst✝¹⁰ : BorelSpace M
inst✝⁹ : ChartedSpace E M
inst✝⁸ : IsManifold I ∞ M
M₃ : Type u
inst✝⁷ : TopologicalSpace M₃
inst✝⁶ : T2Space M₃
inst✝⁵ : CompactSpace M₃
inst✝⁴ : ConnectedSpace M₃
inst✝³ : MeasurableSpace M₃
inst✝² : BorelSpace M₃
inst✝¹ : ChartedSpace (ClosedSmoothModel 3) M₃
inst✝ : IsManifold (closedSmoothModelWithCorners 3) ∞ M₃
g : ClosedSmoothRiemannianMetric 3 M₃
p : M₃
V : Set M₃
hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
φ : M₃ → ℝ
hφ : tsupport φ ⊆ V
hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) 2 φ
z : ↑(extChartAt (closedSmoothModelWithCorners 3) p).target
hz : ↑z ∈ ↑(extChartAt (closedSmoothModelWithCorners 3) p) '' V
G : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := inverseChartPullbackGramMatrixField g p
a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y => (G y)⁻¹
Γ : ClosedSmoothModel 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun y j k l =>
    1 / 2 *
      ∑ m,
        a y j m *
          (coordinateDirectionalDerivative (fun q => G q l m) k y +
              coordinateDirectionalDerivative (fun q => G q k m) l y -
            coordinateDirectionalDerivative (fun q => G q k l) m y)
hsource : tsupport φ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
hu : ContDiff ℝ 2 (ClosedLaplacianStokesProducer.coordinateScalar p φ)
hcompat :
  ∀ (j : Fin 3),
    ∑ k,
        (fderiv ℝ
            (fun y =>
              (fun z =>
                    ↑(rawHausdorffLebesgueScale 3) *
                      VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
                  y *
                (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) y k j)
            ↑z)
          (EuclideanSpace.single k 1) =
      (fun z =>
            ↑(rawHausdorffLebesgueScale 3) *
              VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
          ↑z *
        -∑ k,
            ∑ l,
              (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) (↑z) k l *
                (fun z j k l =>
                    1 / 2 *
                      ∑ m,
                        (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) z j m *
                          (coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y l m) k
                                z +
                              coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k m) l
                                z -
                            coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k l) m
                              z))
                  (↑z) j k l
⊢ (LinearMap.trace ℝ (TangentSpace (closedSmoothModelWithCorners 3) (inverseExtendedChartParametrization p z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization p z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ ↑(g.hessianContinuousAt φ (inverseExtendedChartParametrization p z))) =
    christoffelCoordinateLaplacian a Γ (ClosedLaplacianStokesProducer.coordinateScalar p φ) ↑z
Poincare.DeTurckPrincipalIdentity.christoffel_eq_connection.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace DeTurckPrincipalSecondJet.E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (g : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : DeTurckPrincipalSecondJet.E)
  (hcut : ∀ᶠ (y : ClosedSmoothModel 3) in 𝓝 z, GeodesicTransport.cutoff anchor y = 1)
  (u v : DeTurckPrincipalSecondJet.E) :
  ((GeodesicTransport.chartChristoffelField g anchor z) u) v =
    DeTurckPrincipalIdentity.connection (CovariantDerivative.chartMetric g.inner anchor z)
      (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z) u v
Poincare.DeTurckPrincipalIdentity.koszul_apply (J : DeTurckPrincipalSecondJet.Jet1)
  (u v q : DeTurckPrincipalSecondJet.E) :
  (DeTurckPrincipalIdentity.koszul J u v) q = 1 / 2 * (((J u) v) q + ((J v) u) q - ((J q) u) v)
/tmp/stokes-global-evidence/resisting.lean:333:7: error(lean.unknownIdentifier): Unknown identifier `chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one`
```

### Command

```sh
rg -n 'coordinateDirectionalDerivative|christoffelCoordinateLaplacian|ClosedLaplacianStokes|scalarAt_contMDiffAt_two_of_normalizedRicciFlow|timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three' Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean Poincare/Global/NormalizedFlowScalarRegularity.lean Poincare/Global/MetricFlowJointRegularity.lean | head -35
```

Exit: 0

```text
Poincare/Global/NormalizedFlowScalarRegularity.lean:91:theorem scalarAt_contMDiffAt_two_of_normalizedRicciFlow
Poincare/Global/NormalizedFlowScalarRegularity.lean:142:      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
Poincare/Global/NormalizedFlowScalarRegularity.lean:152:      (fun t ↦ scalarAt_contMDiffAt_two_of_normalizedRicciFlow
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:18:No new declaration is postulated.  `ClosedLaplacianStokes` is a named proposition carrying
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:45:def ClosedLaplacianStokes
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:438:`ClosedLaplacianStokes` statement. -/
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:448:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:461:integral `ClosedLaplacianStokes`. -/
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:477:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:492:boundary reduced completely to `ClosedLaplacianStokes`.  Beyond it, only the
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:509:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:547:/-- `ClosedLaplacianStokes` supplies both pieces needed by the scalar-integral
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:560:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:591:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:606:`ClosedLaplacianStokes`; only the two moving-measure differentiation
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:627:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:28:`ClosedLaplacianStokes` field.
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:48:noncomputable def coordinateDirectionalDerivative
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:55:  fderiv ℝ (coordinateDirectionalDerivative u j) z
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:67:      contractedChristoffel z j * coordinateDirectionalDerivative u j z
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:71:noncomputable def christoffelCoordinateLaplacian
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:79:          christoffel z k i j * coordinateDirectionalDerivative u k z)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:89:      coordinateDirectionalDerivative u j z
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:92:theorem coordinateDirectionalDerivative_contDiff_one
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:94:    ContDiff ℝ 1 (coordinateDirectionalDerivative u j) := by
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:95:  unfold coordinateDirectionalDerivative
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:113:    (coordinateDirectionalDerivative_contDiff_one hu j)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:127:  unfold coordinateMetricFluxComponent coordinateDirectionalDerivative
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:150:    (hdu : ∀ j, DifferentiableAt ℝ (coordinateDirectionalDerivative u j) z)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:157:          coordinateDirectionalDerivative u j z *
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:184:    (hdu : ∀ j, DifferentiableAt ℝ (coordinateDirectionalDerivative u j) z) :
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:190:          coordinateDirectionalDerivative u j z *
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:209:    (hdu : ∀ j, DifferentiableAt ℝ (coordinateDirectionalDerivative u j) z)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:237:        coordinateDirectionalDerivative u j z *
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:242:            contractedChristoffel z j * coordinateDirectionalDerivative u j z) := by
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-11.lean
```

Exit: 0

```text
/tmp/stokes-global-evidence/dependencies-11.lean:89:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility_of_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_cover_global_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.LineDeriv.Basic

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
theorem fderiv_chartWeight
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) :
    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
    (G := fun t : ℝ ↦ G (z + t • v))
    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hdet)
  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq

/-- Differentiating the inverse identity gives the full inverse-matrix derivative. -/
theorem deriv_matrix_inv_entry {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s ↦ A s i j) t)
    (hdet : (A t).det ≠ 0) (i j : Fin n) :
    deriv (fun s ↦ (A s)⁻¹ i j) t =
      -(∑ k, ∑ l, (A t)⁻¹ i k * deriv (fun s ↦ A s k l) t * (A t)⁻¹ l j) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
  let D : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ A s k l) t
  let Q : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ (A s)⁻¹ k l) t
  have hB (k l : Fin n) : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹ k l) t :=
    differentiableAt_matrix_inv_entry_of_entries hA hdet k l
  have hlocal : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 :=
    (differentiableAt_matrix_det_of_entries hA).continuousAt.eventually_ne hdet
  have hprod : Q * A t + B * D = 0 := by
    ext k l
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun m _ ↦ (hB k m).hasDerivAt.mul (hA m l).hasDerivAt)
    have heq : (fun s ↦ ∑ m, (A s)⁻¹ k m * A s m l) =ᶠ[𝓝 t]
        (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ) k l) := by
      filter_upwards [hlocal] with s hs
      exact congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T k l)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
    have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib, Q, B, D] using hzero
  have hab : A t * B = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hq : Q = -(B * D * B) := by
    have hh := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T * B) hprod
    dsimp only at hh
    rw [add_mul, Matrix.mul_assoc, hab, mul_one, zero_mul] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hentry := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T i j) hq
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, Q, B, D] at hentry
  rw [Finset.sum_comm] at hentry
  exact hentry

/-- The inverse Gram entries have the usual spatial derivative. -/
theorem fderiv_chartInverseMetric
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) (i j : Fin n) :
    fderiv ℝ (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z v =
      -(∑ k, ∑ l, (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
        fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y k l) z v *
        (inverseChartPullbackGramMatrixField g p z)⁻¹ l j) := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (k l : Fin n) : DifferentiableAt ℝ (fun y ↦ G y k l) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p k l z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hInv := (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hd := deriv_matrix_inv_entry (A := fun s : ℝ ↦ G (z + s • v)) (t := 0)
    (fun k l ↦ ((hG k l).hasFDerivAt.hasLineDerivAt v).differentiableAt)
    (by simpa only [zero_smul, add_zero] using hdet) i j
  rw [(hInv.hasFDerivAt.hasLineDerivAt v).deriv] at hd
  simp only [zero_smul, add_zero] at hd
  simpa only [((hG _ _).hasFDerivAt.hasLineDerivAt v).deriv] using hd

/-- The three-dimensional finite contraction behind the divergence identity. -/
theorem density_inverse_contraction_three
    (a : Matrix (Fin 3) (Fin 3) ℝ) (ha : a.IsSymm)
    (D : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : ℝ) (j : Fin 3) :
    (∑ k, (((1 / 2 : ℝ) * w * (∑ p, ∑ q, a p q * D k q p)) * a k j +
      w * (-(∑ p, ∑ q, a k p * D k p q * a q j)))) =
    w * (-(∑ k, ∑ l, a k l * ((1 / 2 : ℝ) *
      ∑ m, a j m * (D k l m + D l k m - D m k l)))) := by
  simp only [Fin.sum_univ_three]
  simp only [ha.apply j 0, ha.apply j 1, ha.apply j 2, show a 1 0 = a 0 1 from ha.apply 0 1,
      show a 2 0 = a 0 2 from ha.apply 0 2,
      show a 2 1 = a 1 2 from ha.apply 1 2]
  ring

variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
  [ChartedSpace (ClosedSmoothModel 3) M₃]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]

/-- The genuine density and inverse metric satisfy the chart divergence identity. -/
theorem density_inverseMetric_compatibility
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃) :
    let G := inverseChartPullbackGramMatrixField g p
    let w := fun z ↦ (rawHausdorffLebesgueScale 3 : ℝ) * VolumeDensity.chartVolumeDensity (G z)
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z ↦ (G z)⁻¹
    let Γ := fun z j k l ↦ (1 / 2 : ℝ) * ∑ m, a z j m *
      (coordinateDirectionalDerivative (fun y ↦ G y l m) k z +
       coordinateDirectionalDerivative (fun y ↦ G y k m) l z -
       coordinateDirectionalDerivative (fun y ↦ G y k l) m z)
    ∀ z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target, ∀ j : Fin 3,
      (∑ k, fderiv ℝ (fun y ↦ w y * a y k j) z (EuclideanSpace.single k (1 : ℝ))) =
      w z * (-(∑ k, ∑ l, a z k l * Γ z j k l)) := by
  intro G w a Γ z hz j
  have hW : DifferentiableAt ℝ w z :=
    (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hA (k l : Fin 3) : DifferentiableAt ℝ (fun y ↦ a y k l) z :=
    (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p k l) z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hsymm : (G z).IsSymm := by
    have hp := (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).isHermitian
    rw [inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩] at hp
    exact Matrix.IsSymm.ext (fun k l ↦ by simpa using hp.apply k l)
  let D := fun k l m ↦ fderiv ℝ (fun y ↦ G y l m) z (EuclideanSpace.single k (1 : ℝ))
  calc
    _ = ∑ k, (((1 / 2 : ℝ) * w z * (∑ l, ∑ m, a z l m * D k m l)) * a z k j +
        w z * (-(∑ l, ∑ m, a z k l * D k l m * a z m j))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fderiv_fun_mul hW (hA k j)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_chartWeight g p hz, fderiv_chartInverseMetric g p hz]
      dsimp only [w, a, G, D]
      ring
    _ = _ := density_inverse_contraction_three (a z) hsymm.inv D (w z) j

/-- Global coefficient extensions inherit compatibility wherever they agree locally. -/
theorem density_inverseMetric_compatibility_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
    (w' : ClosedSmoothModel 3 → ℝ)
    (a' : ClosedSmoothModel 3 → Fin 3 → Fin 3 → ℝ) :
    let G := inverseChartPullbackGramMatrixField g p
    let w := fun z ↦ (rawHausdorffLebesgueScale 3 : ℝ) * VolumeDensity.chartVolumeDensity (G z)
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z ↦ (G z)⁻¹
    let Γ := fun z j k l ↦ (1 / 2 : ℝ) * ∑ m, a z j m *
      (coordinateDirectionalDerivative (fun y ↦ G y l m) k z +
       coordinateDirectionalDerivative (fun y ↦ G y k m) l z -
       coordinateDirectionalDerivative (fun y ↦ G y k l) m z)
    ∀ z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target,
      w' =ᶠ[𝓝 z] w → a' =ᶠ[𝓝 z] a → ∀ j : Fin 3,
      (∑ k, fderiv ℝ (fun y ↦ w' y * a' y k j) z (EuclideanSpace.single k (1 : ℝ))) =
      w' z * (-(∑ k, ∑ l, a' z k l * Γ z j k l)) := by
  intro G w a Γ z hz hw ha j
  have hprod (k : Fin 3) :
      (fun y ↦ w' y * a' y k j) =ᶠ[𝓝 z] (fun y ↦ w y * a y k j) := by
    filter_upwards [hw, ha] with y hy hya
    rw [hy, hya]
  simp_rw [(hprod _).fderiv_eq]
  rw [hw.self_of_nhds, ha.self_of_nhds]
  exact density_inverseMetric_compatibility g p z hz j

/-- A shrunk finite cover carries simultaneous global smooth coefficient extensions. -/
theorem exists_shrunk_cover_global_coefficients
    (g : ClosedSmoothRiemannianMetric n M)
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ (V : Fin C.chartCount → Set M)
      (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ)
      (w : Fin C.chartCount → E → ℝ)
      (a : Fin C.chartCount → E → Fin n → Fin n → ℝ),
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      ρ.IsSubordinate V ∧ (∀ i, ContDiff ℝ ∞ (w i)) ∧
      (∀ i j k, ContDiff ℝ ∞ (fun z ↦ a i z j k)) ∧
      (∀ i, ∀ z ∈ (extChartAt I (C.anchor i)) '' closure (V i),
        w i =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
          VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g (C.anchor i) y))) ∧
      (∀ i, ∀ z ∈ (extChartAt I (C.anchor i)) '' closure (V i),
        a i =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g (C.anchor i) y)⁻¹ :
          Matrix (Fin n) (Fin n) ℝ))) := by
  obtain ⟨V, hcover, hopen, hclosure, hcompact, htarget, ρ, hρ⟩ := exists_shrunk_chart_cover C
  choose w a hw ha hwe hae hd using
    fun i ↦ exists_global_coefficients_on_compact g (C.anchor i) (hcompact i) (htarget i)
  exact ⟨V, ρ, w, a, hcover, hopen, hclosure, hcompact, hρ, hw, ha, hwe, hae⟩

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility_of_eventuallyEq
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_cover_global_coefficients
```

### Command

```sh
rg -n '^namespace|^end ' Poincare/Global/LeviCivitaTransport.lean; rg -n 'timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three' Poincare/Global/MetricFlow*
```

Exit: 0

```text
20:namespace CovariantDerivative
551:end ChartConnection
553:end CovariantDerivative
555:namespace Poincare
564:namespace LeviCivitaTransport
778:end LeviCivitaTransport
780:end Poincare
Poincare/Global/MetricFlowJointRegularity.lean:320:theorem timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointRegularity.lean:417:    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointRicciTensorEvolution.lean:61:    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointPinchingEvolution.lean:674:    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointPinchingEvolution.lean:837:    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1395:    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1426:    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Construct simultaneous global coefficients on a shrunk finite cover"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients db8e9175] Construct simultaneous global coefficients on a shrunk finite cover
 1 file changed, 24 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/resisting.lean
```

Exit: 1

```text
/tmp/stokes-global-evidence/resisting.lean:323:75: error: unsolved goals
n : ℕ
M : Type u
inst✝¹⁵ : TopologicalSpace M
inst✝¹⁴ : T2Space M
inst✝¹³ : CompactSpace M
inst✝¹² : ConnectedSpace M
inst✝¹¹ : MeasurableSpace M
inst✝¹⁰ : BorelSpace M
inst✝⁹ : ChartedSpace E M
inst✝⁸ : IsManifold I ∞ M
M₃ : Type u
inst✝⁷ : TopologicalSpace M₃
inst✝⁶ : T2Space M₃
inst✝⁵ : CompactSpace M₃
inst✝⁴ : ConnectedSpace M₃
inst✝³ : MeasurableSpace M₃
inst✝² : BorelSpace M₃
inst✝¹ : ChartedSpace (ClosedSmoothModel 3) M₃
inst✝ : IsManifold (closedSmoothModelWithCorners 3) ∞ M₃
g : ClosedSmoothRiemannianMetric 3 M₃
p : M₃
V : Set M₃
hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
φ : M₃ → ℝ
hφ : tsupport φ ⊆ V
hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) 2 φ
z : ↑(extChartAt (closedSmoothModelWithCorners 3) p).target
hz : ↑z ∈ ↑(extChartAt (closedSmoothModelWithCorners 3) p) '' V
G : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := inverseChartPullbackGramMatrixField g p
a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y => (G y)⁻¹
Γ : ClosedSmoothModel 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun y j k l =>
    1 / 2 *
      ∑ m,
        a y j m *
          (coordinateDirectionalDerivative (fun q => G q l m) k y +
              coordinateDirectionalDerivative (fun q => G q k m) l y -
            coordinateDirectionalDerivative (fun q => G q k l) m y)
hsource : tsupport φ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
hu : ContDiff ℝ 2 (ClosedLaplacianStokesProducer.coordinateScalar p φ)
hcompat :
  ∀ (j : Fin 3),
    ∑ k,
        (fderiv ℝ
            (fun y =>
              (fun z =>
                    ↑(rawHausdorffLebesgueScale 3) *
                      VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
                  y *
                (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) y k j)
            ↑z)
          (EuclideanSpace.single k 1) =
      (fun z =>
            ↑(rawHausdorffLebesgueScale 3) *
              VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
          ↑z *
        -∑ k,
            ∑ l,
              (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) (↑z) k l *
                (fun z j k l =>
                    1 / 2 *
                      ∑ m,
                        (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) z j m *
                          (coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y l m) k
                                z +
                              coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k m) l
                                z -
                            coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k l) m
                              z))
                  (↑z) j k l
⊢ (LinearMap.trace ℝ (TangentSpace (closedSmoothModelWithCorners 3) (inverseExtendedChartParametrization p z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization p z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ ↑(g.hessianContinuousAt φ (inverseExtendedChartParametrization p z))) =
    christoffelCoordinateLaplacian a Γ (ClosedLaplacianStokesProducer.coordinateScalar p φ) ↑z
n : ℕ
M : Type u
inst✝¹⁵ : TopologicalSpace M
inst✝¹⁴ : T2Space M
inst✝¹³ : CompactSpace M
inst✝¹² : ConnectedSpace M
inst✝¹¹ : MeasurableSpace M
inst✝¹⁰ : BorelSpace M
inst✝⁹ : ChartedSpace E M
inst✝⁸ : IsManifold I ∞ M
M₃ : Type u
inst✝⁷ : TopologicalSpace M₃
inst✝⁶ : T2Space M₃
inst✝⁵ : CompactSpace M₃
inst✝⁴ : ConnectedSpace M₃
inst✝³ : MeasurableSpace M₃
inst✝² : BorelSpace M₃
inst✝¹ : ChartedSpace (ClosedSmoothModel 3) M₃
inst✝ : IsManifold (closedSmoothModelWithCorners 3) ∞ M₃
g : ClosedSmoothRiemannianMetric 3 M₃
p : M₃
V : Set M₃
hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
φ : M₃ → ℝ
hφ : tsupport φ ⊆ V
hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) 2 φ
z : ↑(extChartAt (closedSmoothModelWithCorners 3) p).target
hz : ↑z ∈ ↑(extChartAt (closedSmoothModelWithCorners 3) p) '' V
G : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := inverseChartPullbackGramMatrixField g p
a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y => (G y)⁻¹
Γ : ClosedSmoothModel 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun y j k l =>
    1 / 2 *
      ∑ m,
        a y j m *
          (coordinateDirectionalDerivative (fun q => G q l m) k y +
              coordinateDirectionalDerivative (fun q => G q k m) l y -
            coordinateDirectionalDerivative (fun q => G q k l) m y)
hsource : tsupport φ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
hu : ContDiff ℝ 2 (ClosedLaplacianStokesProducer.coordinateScalar p φ)
hcompat :
  ∀ (j : Fin 3),
    ∑ k,
        (fderiv ℝ
            (fun y =>
              (fun z =>
                    ↑(rawHausdorffLebesgueScale 3) *
                      VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
                  y *
                (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) y k j)
            ↑z)
          (EuclideanSpace.single k 1) =
      (fun z =>
            ↑(rawHausdorffLebesgueScale 3) *
              VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
          ↑z *
        -∑ k,
            ∑ l,
              (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) (↑z) k l *
                (fun z j k l =>
                    1 / 2 *
                      ∑ m,
                        (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) z j m *
                          (coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y l m) k
                                z +
                              coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k m) l
                                z -
                            coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k l) m
                              z))
                  (↑z) j k l
⊢ (LinearMap.trace ℝ (TangentSpace (closedSmoothModelWithCorners 3) (inverseExtendedChartParametrization p z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization p z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ ↑(g.hessianContinuousAt φ (inverseExtendedChartParametrization p z))) =
    christoffelCoordinateLaplacian a Γ (ClosedLaplacianStokesProducer.coordinateScalar p φ) ↑z
Poincare.DeTurckPrincipalIdentity.christoffel_eq_connection.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace DeTurckPrincipalSecondJet.E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (g : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : DeTurckPrincipalSecondJet.E)
  (hcut : ∀ᶠ (y : ClosedSmoothModel 3) in 𝓝 z, GeodesicTransport.cutoff anchor y = 1)
  (u v : DeTurckPrincipalSecondJet.E) :
  ((GeodesicTransport.chartChristoffelField g anchor z) u) v =
    DeTurckPrincipalIdentity.connection (CovariantDerivative.chartMetric g.inner anchor z)
      (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z) u v
Poincare.DeTurckPrincipalIdentity.koszul_apply (J : DeTurckPrincipalSecondJet.Jet1)
  (u v q : DeTurckPrincipalSecondJet.E) :
  (DeTurckPrincipalIdentity.koszul J u v) q = 1 / 2 * (((J u) v) q + ((J v) u) q - ((J q) u) v)
Poincare.LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold I ∞ M] (g : ClosedSmoothRiemannianMetric n M)
  (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ) (hG₀pos : ∀ (v : E), v ≠ 0 → 0 < (G₀ v) v) (x₀ : M) (hχ0 : ∀ (z : E), 0 ≤ χ z)
  (hχ1 : ∀ (z : E), χ z ≤ 1)
  (hsupp : ∀ (z : E), χ z ≠ 0 → (mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I x₀).symm) (range ↑I) z).IsInvertible)
  (hbl : Differentiable ℝ (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀))
  (hG₀symm : ∀ (v w : E), (G₀ v) w = (G₀ w) v) {σ : (y : M) → TangentSpace I y} {y : M}
  (hy : y ∈ (extChartAt I x₀).source) (hχone : ∀ᶠ (z' : E) in 𝓝 (↑(extChartAt I x₀) y), χ z' = 1)
  (hσ : MDiffAtTangentField σ y) (v : TangentSpace I y) :
  CovariantDerivative.chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g.inner ⋯ x₀ hχ0 hχ1 hsupp σ hy v =
    (↑(LeviCivitaExistence.closedLeviCivitaConnection g) σ y) v
```

### Command

```sh
sed -n "44,81p" Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean && sed -n "388,447p" Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean
```

Exit: 0

```text
local notation "E" => ClosedSmoothModel n

/-- The `j`-th Euclidean directional derivative in the standard coordinate
basis. -/
noncomputable def coordinateDirectionalDerivative
    (u : E → ℝ) (j : Fin n) (z : E) : ℝ :=
  fderiv ℝ u z (EuclideanSpace.single j (1 : ℝ))

/-- The iterated `(i,j)` coordinate derivative. -/
noncomputable def coordinateSecondDerivative
    (u : E → ℝ) (i j : Fin n) (z : E) : ℝ :=
  fderiv ℝ (coordinateDirectionalDerivative u j) z
    (EuclideanSpace.single i (1 : ℝ))

/-- Coordinate Laplacian written using inverse metric coefficients and the
contracted Christoffel drift. -/
noncomputable def contractedCoordinateLaplacian
    (inverseMetric : E → Fin n → Fin n → ℝ)
    (contractedChristoffel : E → Fin n → ℝ)
    (u : E → ℝ) (z : E) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n,
      inverseMetric z i j * coordinateSecondDerivative u i j z) +
    ∑ j : Fin n,
      contractedChristoffel z j * coordinateDirectionalDerivative u j z

/-- The conventional Christoffel-coordinate expression
`g^{ij} (partial_i partial_j u - Gamma^k_ij partial_k u)`. -/
noncomputable def christoffelCoordinateLaplacian
    (inverseMetric : E → Fin n → Fin n → ℝ)
    (christoffel : E → Fin n → Fin n → Fin n → ℝ)
    (u : E → ℝ) (z : E) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    inverseMetric z i j *
      (coordinateSecondDerivative u i j z -
        ∑ k : Fin n,
          christoffel z k i j * coordinateDirectionalDerivative u k z)

/-- The metric flux with density weight `w`: its `i`-th component is
structure FiniteSubordinateHausdorffLaplacianGeometry
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) where
  chartCount : ℕ
  coordinateDomain : Fin chartCount → Set E
  coordinateDomain_measurable : ∀ i, MeasurableSet (coordinateDomain i)
  inverseChart : (i : Fin chartCount) → coordinateDomain i → M
  inverseChart_measurable : ∀ i, Measurable (inverseChart i)
  chartRegion : Fin chartCount → Set M
  chartRegion_isOpen : ∀ i, IsOpen (chartRegion i)
  density : (i : Fin chartCount) → coordinateDomain i → ℝ
  density_nonneg : ∀ i,
    0 ≤ᵐ[coordinateLebesgueMeasure (coordinateDomain i)] density i
  density_integrable : ∀ i,
    Integrable (density i) (coordinateLebesgueMeasure (coordinateDomain i))
  chartMeasure : ∀ i,
    HausdorffChartDensityEquality g
      (coordinateDomain i) (inverseChart i) (chartRegion i) (density i)
  partition : SmoothPartitionOfUnity (Fin chartCount) I M Set.univ
  partition_subordinate : partition.IsSubordinate chartRegion
  f_contMDiff_two : ContMDiff I 𝓘(ℝ) 2 f
  coordinateRepresentative : Fin chartCount → E → ℝ
  coordinateRepresentative_eq : ∀ i (z : coordinateDomain i),
    coordinateRepresentative i z =
      partition i (inverseChart i z) * f (inverseChart i z)
  coordinateRepresentative_contDiff_two : ∀ i,
    ContDiff ℝ 2 (coordinateRepresentative i)
  coordinateRepresentative_hasCompactSupport : ∀ i,
    HasCompactSupport (coordinateRepresentative i)
  coordinateRepresentative_tsupport_subset_coordinateDomain : ∀ i,
    tsupport (coordinateRepresentative i) ⊆ coordinateDomain i
  weight : Fin chartCount → E → ℝ
  weight_contDiff_one : ∀ i, ContDiff ℝ 1 (weight i)
  weight_eq_density : ∀ i (z : coordinateDomain i),
    weight i z = (rawHausdorffLebesgueScale n : ℝ) * density i z
  inverseMetric : Fin chartCount → E → Fin n → Fin n → ℝ
  inverseMetric_contDiff_one : ∀ i a b,
    ContDiff ℝ 1 (fun z ↦ inverseMetric i z a b)
  christoffel : Fin chartCount → E → Fin n → Fin n → Fin n → ℝ
  contractedChristoffel : Fin chartCount → E → Fin n → ℝ
  contractedChristoffel_eq : ∀ i (z : coordinateDomain i) k,
    contractedChristoffel i z k =
      -(∑ a : Fin n, ∑ b : Fin n,
        inverseMetric i z a b * christoffel i z k a b)
  density_inverseMetric_compatibility : ∀ i
      (z : coordinateDomain i) (j : Fin n),
    (∑ a : Fin n,
      fderiv ℝ (fun y ↦ weight i y * inverseMetric i y a j) z
        (EuclideanSpace.single a (1 : ℝ))) =
      weight i z * contractedChristoffel i z j
  intrinsicCoordinateLaplacian_eq : ∀ i
      (z : coordinateDomain i),
    g.laplacianAt
        (fun x : M ↦ partition i x * f x) (inverseChart i z) =
      christoffelCoordinateLaplacian
        (inverseMetric i) (christoffel i)
          (coordinateRepresentative i) z
  localizedLaplacian_aestronglyMeasurable : ∀ i,
    AEStronglyMeasurable
      (fun x : M ↦
        g.laplacianAt (fun y : M ↦ partition i y * f y) x)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/dependencies-11.lean
```

Exit: 0

```text
'Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility_of_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_cover_global_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Dependency probe source:

```lean
import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.LineDeriv.Basic

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
theorem fderiv_chartWeight
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) :
    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
    (G := fun t : ℝ ↦ G (z + t • v))
    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hdet)
  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq

/-- Differentiating the inverse identity gives the full inverse-matrix derivative. -/
theorem deriv_matrix_inv_entry {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s ↦ A s i j) t)
    (hdet : (A t).det ≠ 0) (i j : Fin n) :
    deriv (fun s ↦ (A s)⁻¹ i j) t =
      -(∑ k, ∑ l, (A t)⁻¹ i k * deriv (fun s ↦ A s k l) t * (A t)⁻¹ l j) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
  let D : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ A s k l) t
  let Q : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ (A s)⁻¹ k l) t
  have hB (k l : Fin n) : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹ k l) t :=
    differentiableAt_matrix_inv_entry_of_entries hA hdet k l
  have hlocal : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 :=
    (differentiableAt_matrix_det_of_entries hA).continuousAt.eventually_ne hdet
  have hprod : Q * A t + B * D = 0 := by
    ext k l
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun m _ ↦ (hB k m).hasDerivAt.mul (hA m l).hasDerivAt)
    have heq : (fun s ↦ ∑ m, (A s)⁻¹ k m * A s m l) =ᶠ[𝓝 t]
        (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ) k l) := by
      filter_upwards [hlocal] with s hs
      exact congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T k l)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
    have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib, Q, B, D] using hzero
  have hab : A t * B = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hq : Q = -(B * D * B) := by
    have hh := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T * B) hprod
    dsimp only at hh
    rw [add_mul, Matrix.mul_assoc, hab, mul_one, zero_mul] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hentry := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T i j) hq
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, Q, B, D] at hentry
  rw [Finset.sum_comm] at hentry
  exact hentry

/-- The inverse Gram entries have the usual spatial derivative. -/
theorem fderiv_chartInverseMetric
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) (i j : Fin n) :
    fderiv ℝ (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z v =
      -(∑ k, ∑ l, (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
        fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y k l) z v *
        (inverseChartPullbackGramMatrixField g p z)⁻¹ l j) := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (k l : Fin n) : DifferentiableAt ℝ (fun y ↦ G y k l) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p k l z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hInv := (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hd := deriv_matrix_inv_entry (A := fun s : ℝ ↦ G (z + s • v)) (t := 0)
    (fun k l ↦ ((hG k l).hasFDerivAt.hasLineDerivAt v).differentiableAt)
    (by simpa only [zero_smul, add_zero] using hdet) i j
  rw [(hInv.hasFDerivAt.hasLineDerivAt v).deriv] at hd
  simp only [zero_smul, add_zero] at hd
  simpa only [((hG _ _).hasFDerivAt.hasLineDerivAt v).deriv] using hd

/-- The three-dimensional finite contraction behind the divergence identity. -/
theorem density_inverse_contraction_three
    (a : Matrix (Fin 3) (Fin 3) ℝ) (ha : a.IsSymm)
    (D : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : ℝ) (j : Fin 3) :
    (∑ k, (((1 / 2 : ℝ) * w * (∑ p, ∑ q, a p q * D k q p)) * a k j +
      w * (-(∑ p, ∑ q, a k p * D k p q * a q j)))) =
    w * (-(∑ k, ∑ l, a k l * ((1 / 2 : ℝ) *
      ∑ m, a j m * (D k l m + D l k m - D m k l)))) := by
  simp only [Fin.sum_univ_three]
  simp only [ha.apply j 0, ha.apply j 1, ha.apply j 2, show a 1 0 = a 0 1 from ha.apply 0 1,
      show a 2 0 = a 0 2 from ha.apply 0 2,
      show a 2 1 = a 1 2 from ha.apply 1 2]
  ring

variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
  [ChartedSpace (ClosedSmoothModel 3) M₃]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]

/-- The genuine density and inverse metric satisfy the chart divergence identity. -/
theorem density_inverseMetric_compatibility
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃) :
    let G := inverseChartPullbackGramMatrixField g p
    let w := fun z ↦ (rawHausdorffLebesgueScale 3 : ℝ) * VolumeDensity.chartVolumeDensity (G z)
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z ↦ (G z)⁻¹
    let Γ := fun z j k l ↦ (1 / 2 : ℝ) * ∑ m, a z j m *
      (coordinateDirectionalDerivative (fun y ↦ G y l m) k z +
       coordinateDirectionalDerivative (fun y ↦ G y k m) l z -
       coordinateDirectionalDerivative (fun y ↦ G y k l) m z)
    ∀ z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target, ∀ j : Fin 3,
      (∑ k, fderiv ℝ (fun y ↦ w y * a y k j) z (EuclideanSpace.single k (1 : ℝ))) =
      w z * (-(∑ k, ∑ l, a z k l * Γ z j k l)) := by
  intro G w a Γ z hz j
  have hW : DifferentiableAt ℝ w z :=
    (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hA (k l : Fin 3) : DifferentiableAt ℝ (fun y ↦ a y k l) z :=
    (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p k l) z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hsymm : (G z).IsSymm := by
    have hp := (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).isHermitian
    rw [inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩] at hp
    exact Matrix.IsSymm.ext (fun k l ↦ by simpa using hp.apply k l)
  let D := fun k l m ↦ fderiv ℝ (fun y ↦ G y l m) z (EuclideanSpace.single k (1 : ℝ))
  calc
    _ = ∑ k, (((1 / 2 : ℝ) * w z * (∑ l, ∑ m, a z l m * D k m l)) * a z k j +
        w z * (-(∑ l, ∑ m, a z k l * D k l m * a z m j))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fderiv_fun_mul hW (hA k j)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_chartWeight g p hz, fderiv_chartInverseMetric g p hz]
      dsimp only [w, a, G, D]
      ring
    _ = _ := density_inverse_contraction_three (a z) hsymm.inv D (w z) j

/-- Global coefficient extensions inherit compatibility wherever they agree locally. -/
theorem density_inverseMetric_compatibility_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
    (w' : ClosedSmoothModel 3 → ℝ)
    (a' : ClosedSmoothModel 3 → Fin 3 → Fin 3 → ℝ) :
    let G := inverseChartPullbackGramMatrixField g p
    let w := fun z ↦ (rawHausdorffLebesgueScale 3 : ℝ) * VolumeDensity.chartVolumeDensity (G z)
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z ↦ (G z)⁻¹
    let Γ := fun z j k l ↦ (1 / 2 : ℝ) * ∑ m, a z j m *
      (coordinateDirectionalDerivative (fun y ↦ G y l m) k z +
       coordinateDirectionalDerivative (fun y ↦ G y k m) l z -
       coordinateDirectionalDerivative (fun y ↦ G y k l) m z)
    ∀ z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target,
      w' =ᶠ[𝓝 z] w → a' =ᶠ[𝓝 z] a → ∀ j : Fin 3,
      (∑ k, fderiv ℝ (fun y ↦ w' y * a' y k j) z (EuclideanSpace.single k (1 : ℝ))) =
      w' z * (-(∑ k, ∑ l, a' z k l * Γ z j k l)) := by
  intro G w a Γ z hz hw ha j
  have hprod (k : Fin 3) :
      (fun y ↦ w' y * a' y k j) =ᶠ[𝓝 z] (fun y ↦ w y * a y k j) := by
    filter_upwards [hw, ha] with y hy hya
    rw [hy, hya]
  simp_rw [(hprod _).fderiv_eq]
  rw [hw.self_of_nhds, ha.self_of_nhds]
  exact density_inverseMetric_compatibility g p z hz j

/-- A shrunk finite cover carries simultaneous global smooth coefficient extensions. -/
theorem exists_shrunk_cover_global_coefficients
    (g : ClosedSmoothRiemannianMetric n M)
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ (V : Fin C.chartCount → Set M)
      (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ)
      (w : Fin C.chartCount → E → ℝ)
      (a : Fin C.chartCount → E → Fin n → Fin n → ℝ),
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      ρ.IsSubordinate V ∧ (∀ i, ContDiff ℝ ∞ (w i)) ∧
      (∀ i j k, ContDiff ℝ ∞ (fun z ↦ a i z j k)) ∧
      (∀ i, ∀ z ∈ (extChartAt I (C.anchor i)) '' closure (V i),
        w i =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
          VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g (C.anchor i) y))) ∧
      (∀ i, ∀ z ∈ (extChartAt I (C.anchor i)) '' closure (V i),
        a i =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g (C.anchor i) y)⁻¹ :
          Matrix (Fin n) (Fin n) ℝ))) := by
  obtain ⟨V, hcover, hopen, hclosure, hcompact, htarget, ρ, hρ⟩ := exists_shrunk_chart_cover C
  choose w a hw ha hwe hae hd using
    fun i ↦ exists_global_coefficients_on_compact g (C.anchor i) (hcompact i) (htarget i)
  exact ⟨V, ρ, w, a, hcover, hopen, hclosure, hcompact, hρ, hw, ha, hwe, hae⟩

end Poincare.ClosedLaplacianStokesGlobalCoefficients

#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_global_coefficients_on_compact
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_chart_cover
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartWeight
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.deriv_matrix_inv_entry
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.fderiv_chartInverseMetric
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverse_contraction_three
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility_of_eventuallyEq
#print axioms Poincare.ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_cover_global_coefficients
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/stokes-global-evidence/flow.lean
```

Exit: 0

```text
Poincare.ClosedLaplacianStokesProducer.geometry_of_coordinate_coefficients.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M] (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
  (C : FiniteExtendedChartCover) (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M)
  (hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source) (w : Fin C.chartCount → E → ℝ)
  (a : Fin C.chartCount → E → Fin n → Fin n → ℝ) (Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ)
  (hw : ∀ (i : Fin C.chartCount), ContDiff ℝ 1 (w i))
  (ha : ∀ (i : Fin C.chartCount) (j k : Fin n), ContDiff ℝ 1 fun z => a i z j k)
  (hweight :
    ∀ (i : Fin C.chartCount) (z : ↑(extChartAt I (C.anchor i)).target),
      w i ↑z = ↑(rawHausdorffLebesgueScale n) * inverseChartPullbackVolumeDensity g (C.anchor i) z)
  (hcompat :
    ∀ (i : Fin C.chartCount) (z : ↑(extChartAt I (C.anchor i)).target) (j : Fin n),
      ∑ k, (fderiv ℝ (fun y => w i y * a i y k j) ↑z) (EuclideanSpace.single k 1) =
        w i ↑z * -∑ k, ∑ l, a i (↑z) k l * Γ i (↑z) j k l)
  (hcoord :
    ∀ (i : Fin C.chartCount) (z : ↑(extChartAt I (C.anchor i)).target),
      g.laplacianAt (fun x => (ρ i) x * f x) (inverseExtendedChartParametrization (C.anchor i) z) =
        christoffelCoordinateLaplacian (a i) (Γ i)
          (ClosedLaplacianStokesProducer.coordinateScalar (C.anchor i) fun x => (ρ i) x * f x) ↑z) :
  FiniteSubordinateHausdorffLaplacianGeometry g f
Poincare.FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M] {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
  (A : FiniteSubordinateHausdorffLaplacianGeometry g f) : ClosedLaplacianStokes g f
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check && git add Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean && git commit -m "Remove unused assumptions from the finite cover shrinking lemma"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-global-coefficients 1e104311] Remove unused assumptions from the finite cover shrinking lemma
 1 file changed, 1 insertion(+)
```

### Command

```sh
git log --oneline 28c6bb478e20ddcd8049d2baa7e4ad1585b48f42..HEAD && git diff --stat 28c6bb478e20ddcd8049d2baa7e4ad1585b48f42..HEAD && git diff --check 28c6bb478e20ddcd8049d2baa7e4ad1585b48f42..HEAD && git status --short --branch
```

Exit: 0

```text
1e104311 Remove unused assumptions from the finite cover shrinking lemma
db8e9175 Construct simultaneous global coefficients on a shrunk finite cover
3c3b7cd0 Transfer the divergence identity to locally agreeing global coefficients
f6c39b46 Prove the genuine chart density divergence identity in dimension three
865e199e Prove the three-dimensional density-Christoffel contraction
e25cb170 Differentiate the inverse Gram entries in spatial directions
fd96c61b Derive the inverse-matrix entry derivative from the inverse identity
3d89675d Differentiate the genuine chart weight in spatial directions
602e53b5 Shrink finite chart covers with compact coordinate closures
97e1acec Extend genuine chart coefficients smoothly near compact sets
51d21f04 Construct smooth cutoffs near compact coordinate sets
fc9c641f Extend chartwise smooth scalars by cutoff multiplication
 .../ClosedLaplacianStokesGlobalCoefficients.lean   | 307 +++++++++++++++++++++
 1 file changed, 307 insertions(+)
## worker/closed-laplacian-stokes-global-coefficients
```

### Command

```sh
git diff 28c6bb478e20ddcd8049d2baa7e4ad1585b48f42..HEAD -- Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 0

```text
diff --git a/Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean b/Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
new file mode 100644
index 00000000..5525156d
--- /dev/null
+++ b/Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
@@ -0,0 +1,307 @@
+import Poincare.Global.ClosedLaplacianStokesProducer
+import Mathlib.Topology.ShrinkingLemma
+import Mathlib.Analysis.Calculus.LineDeriv.Basic
+
+noncomputable section
+open Bundle FiberBundle Filter MeasureTheory Set
+open scoped Manifold ContDiff Topology ENNReal NNReal
+set_option autoImplicit false
+universe u
+namespace Poincare.ClosedLaplacianStokesGlobalCoefficients
+
+variable {n : ℕ}
+local notation "E" => ClosedSmoothModel n
+
+/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
+theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
+    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
+    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
+  apply contDiff_iff_contDiffAt.mpr
+  intro z
+  by_cases hz : z ∈ U
+  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
+  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
+    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
+    filter_upwards [hzero] with y hy
+    simp only [hy, Pi.zero_apply, zero_mul]
+
+/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
+theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
+    (hU : IsOpen U) (hKU : K ⊆ U) :
+    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
+      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
+  obtain ⟨χ, hzero, hone, hbounds⟩ :=
+    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
+      hU.isClosed_compl hK.isClosed
+      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
+  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
+  · intro z hz
+    by_contra hzU
+    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
+      hzero.filter_mono (nhds_le_nhdsSet hzU)
+    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
+  · intro z hz
+    exact hone.filter_mono (nhds_le_nhdsSet hz)
+
+variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
+  [MeasurableSpace M] [BorelSpace M]
+  [ChartedSpace (ClosedSmoothModel n) M]
+  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
+local notation "I" => closedSmoothModelWithCorners n
+
+/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
+theorem exists_global_coefficients_on_compact
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
+    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
+    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
+      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
+      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
+        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
+      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
+        Matrix (Fin n) (Fin n) ℝ))) ∧
+      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
+        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
+  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
+    (isOpen_extChartAt_target p) hKU
+  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
+    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
+  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
+  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
+  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
+      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
+  · intro i j
+    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
+      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
+  · intro z hz
+    filter_upwards [hone z hz] with y hy
+    simp only [hy, one_mul, W]
+  · intro z hz
+    filter_upwards [hone z hz] with y hy
+    funext i j
+    change χ y * A y i j = A y i j
+    rw [hy, one_mul]
+  · intro z hz
+    change χ z * W z = _
+    rw [(hone z hz).self_of_nhds, one_mul]
+    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z
+
+omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
+/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
+theorem exists_shrunk_chart_cover
+    (C : FiniteExtendedChartCover (n := n) (M := M)) :
+    ∃ V : Fin C.chartCount → Set M,
+      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
+      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
+      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
+      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
+        (extChartAt I (C.anchor i)).target) ∧
+      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
+  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
+    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
+    (fun _ ↦ Set.toFinite _) C.sources_cover
+  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
+  · intro i
+    exact isClosed_closure.isCompact.image_of_continuousOn
+      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
+  · intro i
+    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
+      (hclosure i hx))
+  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
+    rw [hcover]
+
+/-- Jacobi's density formula in any spatial coordinate direction. -/
+theorem fderiv_chartWeight
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
+    (hz : z ∈ (extChartAt I p).target) (v : E) :
+    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
+        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
+      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
+        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
+        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
+          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
+  let G := inverseChartPullbackGramMatrixField g p
+  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
+    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
+      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
+  have hdet : (G z).det ≠ 0 := by
+    dsimp [G]
+    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
+    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
+  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
+    (G := fun t : ℝ ↦ G (z + t • v))
+    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
+    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
+    (by simpa only [zero_smul, add_zero] using hdet)
+  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
+    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
+  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
+    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
+  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq
+
+/-- Differentiating the inverse identity gives the full inverse-matrix derivative. -/
+theorem deriv_matrix_inv_entry {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
+    (hA : ∀ i j, DifferentiableAt ℝ (fun s ↦ A s i j) t)
+    (hdet : (A t).det ≠ 0) (i j : Fin n) :
+    deriv (fun s ↦ (A s)⁻¹ i j) t =
+      -(∑ k, ∑ l, (A t)⁻¹ i k * deriv (fun s ↦ A s k l) t * (A t)⁻¹ l j) := by
+  classical
+  let B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
+  let D : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ A s k l) t
+  let Q : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ (A s)⁻¹ k l) t
+  have hB (k l : Fin n) : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹ k l) t :=
+    differentiableAt_matrix_inv_entry_of_entries hA hdet k l
+  have hlocal : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 :=
+    (differentiableAt_matrix_det_of_entries hA).continuousAt.eventually_ne hdet
+  have hprod : Q * A t + B * D = 0 := by
+    ext k l
+    have hd := HasDerivAt.fun_sum (u := Finset.univ)
+      (fun m _ ↦ (hB k m).hasDerivAt.mul (hA m l).hasDerivAt)
+    have heq : (fun s ↦ ∑ m, (A s)⁻¹ k m * A s m l) =ᶠ[𝓝 t]
+        (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ) k l) := by
+      filter_upwards [hlocal] with s hs
+      exact congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T k l)
+        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
+    have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
+    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
+      ← Finset.sum_add_distrib, Q, B, D] using hzero
+  have hab : A t * B = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
+  have hq : Q = -(B * D * B) := by
+    have hh := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T * B) hprod
+    dsimp only at hh
+    rw [add_mul, Matrix.mul_assoc, hab, mul_one, zero_mul] at hh
+    exact eq_neg_of_add_eq_zero_left hh
+  have hentry := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T i j) hq
+  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, Q, B, D] at hentry
+  rw [Finset.sum_comm] at hentry
+  exact hentry
+
+/-- The inverse Gram entries have the usual spatial derivative. -/
+theorem fderiv_chartInverseMetric
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
+    (hz : z ∈ (extChartAt I p).target) (v : E) (i j : Fin n) :
+    fderiv ℝ (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z v =
+      -(∑ k, ∑ l, (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
+        fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y k l) z v *
+        (inverseChartPullbackGramMatrixField g p z)⁻¹ l j) := by
+  let G := inverseChartPullbackGramMatrixField g p
+  have hG (k l : Fin n) : DifferentiableAt ℝ (fun y ↦ G y k l) z :=
+    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p k l z hz).contDiffAt
+      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
+  have hdet : (G z).det ≠ 0 := by
+    dsimp [G]
+    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
+    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
+  have hInv := (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
+  have hd := deriv_matrix_inv_entry (A := fun s : ℝ ↦ G (z + s • v)) (t := 0)
+    (fun k l ↦ ((hG k l).hasFDerivAt.hasLineDerivAt v).differentiableAt)
+    (by simpa only [zero_smul, add_zero] using hdet) i j
+  rw [(hInv.hasFDerivAt.hasLineDerivAt v).deriv] at hd
+  simp only [zero_smul, add_zero] at hd
+  simpa only [((hG _ _).hasFDerivAt.hasLineDerivAt v).deriv] using hd
+
+/-- The three-dimensional finite contraction behind the divergence identity. -/
+theorem density_inverse_contraction_three
+    (a : Matrix (Fin 3) (Fin 3) ℝ) (ha : a.IsSymm)
+    (D : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : ℝ) (j : Fin 3) :
+    (∑ k, (((1 / 2 : ℝ) * w * (∑ p, ∑ q, a p q * D k q p)) * a k j +
+      w * (-(∑ p, ∑ q, a k p * D k p q * a q j)))) =
+    w * (-(∑ k, ∑ l, a k l * ((1 / 2 : ℝ) *
+      ∑ m, a j m * (D k l m + D l k m - D m k l)))) := by
+  simp only [Fin.sum_univ_three]
+  simp only [ha.apply j 0, ha.apply j 1, ha.apply j 2, show a 1 0 = a 0 1 from ha.apply 0 1,
+      show a 2 0 = a 0 2 from ha.apply 0 2,
+      show a 2 1 = a 1 2 from ha.apply 1 2]
+  ring
+
+variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
+  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
+  [ChartedSpace (ClosedSmoothModel 3) M₃]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
+
+/-- The genuine density and inverse metric satisfy the chart divergence identity. -/
+theorem density_inverseMetric_compatibility
+    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃) :
+    let G := inverseChartPullbackGramMatrixField g p
+    let w := fun z ↦ (rawHausdorffLebesgueScale 3 : ℝ) * VolumeDensity.chartVolumeDensity (G z)
+    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z ↦ (G z)⁻¹
+    let Γ := fun z j k l ↦ (1 / 2 : ℝ) * ∑ m, a z j m *
+      (coordinateDirectionalDerivative (fun y ↦ G y l m) k z +
+       coordinateDirectionalDerivative (fun y ↦ G y k m) l z -
+       coordinateDirectionalDerivative (fun y ↦ G y k l) m z)
+    ∀ z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target, ∀ j : Fin 3,
+      (∑ k, fderiv ℝ (fun y ↦ w y * a y k j) z (EuclideanSpace.single k (1 : ℝ))) =
+      w z * (-(∑ k, ∑ l, a z k l * Γ z j k l)) := by
+  intro G w a Γ z hz j
+  have hW : DifferentiableAt ℝ w z :=
+    (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
+      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
+  have hA (k l : Fin 3) : DifferentiableAt ℝ (fun y ↦ a y k l) z :=
+    (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p k l) z hz).contDiffAt
+      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
+  have hsymm : (G z).IsSymm := by
+    have hp := (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).isHermitian
+    rw [inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩] at hp
+    exact Matrix.IsSymm.ext (fun k l ↦ by simpa using hp.apply k l)
+  let D := fun k l m ↦ fderiv ℝ (fun y ↦ G y l m) z (EuclideanSpace.single k (1 : ℝ))
+  calc
+    _ = ∑ k, (((1 / 2 : ℝ) * w z * (∑ l, ∑ m, a z l m * D k m l)) * a z k j +
+        w z * (-(∑ l, ∑ m, a z k l * D k l m * a z m j))) := by
+      apply Finset.sum_congr rfl
+      intro k _
+      rw [fderiv_fun_mul hW (hA k j)]
+      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
+      rw [fderiv_chartWeight g p hz, fderiv_chartInverseMetric g p hz]
+      dsimp only [w, a, G, D]
+      ring
+    _ = _ := density_inverse_contraction_three (a z) hsymm.inv D (w z) j
+
+/-- Global coefficient extensions inherit compatibility wherever they agree locally. -/
+theorem density_inverseMetric_compatibility_of_eventuallyEq
+    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
+    (w' : ClosedSmoothModel 3 → ℝ)
+    (a' : ClosedSmoothModel 3 → Fin 3 → Fin 3 → ℝ) :
+    let G := inverseChartPullbackGramMatrixField g p
+    let w := fun z ↦ (rawHausdorffLebesgueScale 3 : ℝ) * VolumeDensity.chartVolumeDensity (G z)
+    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun z ↦ (G z)⁻¹
+    let Γ := fun z j k l ↦ (1 / 2 : ℝ) * ∑ m, a z j m *
+      (coordinateDirectionalDerivative (fun y ↦ G y l m) k z +
+       coordinateDirectionalDerivative (fun y ↦ G y k m) l z -
+       coordinateDirectionalDerivative (fun y ↦ G y k l) m z)
+    ∀ z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target,
+      w' =ᶠ[𝓝 z] w → a' =ᶠ[𝓝 z] a → ∀ j : Fin 3,
+      (∑ k, fderiv ℝ (fun y ↦ w' y * a' y k j) z (EuclideanSpace.single k (1 : ℝ))) =
+      w' z * (-(∑ k, ∑ l, a' z k l * Γ z j k l)) := by
+  intro G w a Γ z hz hw ha j
+  have hprod (k : Fin 3) :
+      (fun y ↦ w' y * a' y k j) =ᶠ[𝓝 z] (fun y ↦ w y * a y k j) := by
+    filter_upwards [hw, ha] with y hy hya
+    rw [hy, hya]
+  simp_rw [(hprod _).fderiv_eq]
+  rw [hw.self_of_nhds, ha.self_of_nhds]
+  exact density_inverseMetric_compatibility g p z hz j
+
+/-- A shrunk finite cover carries simultaneous global smooth coefficient extensions. -/
+theorem exists_shrunk_cover_global_coefficients
+    (g : ClosedSmoothRiemannianMetric n M)
+    (C : FiniteExtendedChartCover (n := n) (M := M)) :
+    ∃ (V : Fin C.chartCount → Set M)
+      (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ)
+      (w : Fin C.chartCount → E → ℝ)
+      (a : Fin C.chartCount → E → Fin n → Fin n → ℝ),
+      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
+      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
+      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
+      ρ.IsSubordinate V ∧ (∀ i, ContDiff ℝ ∞ (w i)) ∧
+      (∀ i j k, ContDiff ℝ ∞ (fun z ↦ a i z j k)) ∧
+      (∀ i, ∀ z ∈ (extChartAt I (C.anchor i)) '' closure (V i),
+        w i =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
+          VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g (C.anchor i) y))) ∧
+      (∀ i, ∀ z ∈ (extChartAt I (C.anchor i)) '' closure (V i),
+        a i =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g (C.anchor i) y)⁻¹ :
+          Matrix (Fin n) (Fin n) ℝ))) := by
+  obtain ⟨V, hcover, hopen, hclosure, hcompact, htarget, ρ, hρ⟩ := exists_shrunk_chart_cover C
+  choose w a hw ha hwe hae hd using
+    fun i ↦ exists_global_coefficients_on_compact g (C.anchor i) (hcompact i) (htarget i)
+  exact ⟨V, ρ, w, a, hcover, hopen, hclosure, hcompact, hρ, hw, ha, hwe, hae⟩
+
+end Poincare.ClosedLaplacianStokesGlobalCoefficients
```

### Command

```sh
rg -n 'closedLaplacianStokes_of_contMDiff_two|theorem.*forward|theorem.*flow' Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
```

Exit: 1

```text
```

### Final staged scope and whitespace check

```sh
git diff --cached --check && git diff --check && git diff --name-status 28c6bb478e20ddcd8049d2baa7e4ad1585b48f42 && git status --short --branch
```

Exit: 0

```text
A	Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean
A	harness/reports/closed-laplacian-stokes-global-coefficients_blocked.md
## worker/closed-laplacian-stokes-global-coefficients
A  harness/reports/closed-laplacian-stokes-global-coefficients_blocked.md
```
