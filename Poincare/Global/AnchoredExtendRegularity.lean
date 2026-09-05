import Poincare.Global.RicciFlow

/-!
# Regularity of the canonical anchored tangent extension

On the source of the preferred chart at its anchor, `FiberBundle.extend` has
constant fiber coordinates in the anchor trivialization.  This gives regularity
on the full preferred-chart source, rather than only on an unspecified
neighborhood supplied by `FiberBundle.exists_contMDiffOn_extend`.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace Poincare

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
The tangent extension anchored at `x` is `C^k` on the full source of the
preferred chart at `x`.
-/
theorem anchoredExtend_contMDiffOn_source
    {k : ℕ∞ω} [ENat.LEInfty k] (x : M) (v : TM x) :
    ContMDiffOn I ((I).prod 𝓘(ℝ, E)) k
      (T% (extend E v)) (extChartAt I x).source := by
  let t := trivializationAt E TM x
  have hbase : t.baseSet = (extChartAt I x).source := by
    simp [t, TangentBundle.trivializationAt_baseSet]
  rw [← hbase]
  suffices
      ContMDiffOn I 𝓘(ℝ, E) k
        (fun y ↦ (t ⟨y, extend E v y⟩).2) t.baseSet by
    intro y hy
    rw [t.contMDiffWithinAt_section _ hy]
    exact this y hy
  let w : E := (t ⟨x, v⟩).2
  have hw : ContMDiffOn I 𝓘(ℝ, E) k (fun _y ↦ w) t.baseSet :=
    contMDiffOn_const
  exact hw.congr (fun y hy ↦ by
    change (t ⟨y, t.symm y w⟩).2 = w
    have hpair : t ⟨y, t.symm y w⟩ = (y, w) :=
      t.apply_mk_symm hy w
    have hsnd := congrArg (fun p : M × E ↦ p.2) hpair
    simpa only using hsnd)

/--
At every point of the anchor chart source, the anchored tangent extension is
`C^k` in a neighborhood of that point.
-/
theorem anchoredExtend_contMDiffAt_of_mem_source
    {k : ℕ∞ω} [ENat.LEInfty k] (x : M) (v : TM x) {y : M}
    (hy : y ∈ (extChartAt I x).source) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, E)) k (T% (extend E v)) y :=
  (anchoredExtend_contMDiffOn_source (k := k) x v).contMDiffAt
    ((isOpen_extChartAt_source x).mem_nhds hy)

/--
The anchored tangent extension is differentiable at every point of its anchor
chart source.
-/
theorem anchoredExtend_mdifferentiableAt_of_mem_source
    (x : M) (v : TM x) {y : M}
    (hy : y ∈ (extChartAt I x).source) :
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E v)) y :=
  (anchoredExtend_contMDiffAt_of_mem_source (k := 1) x v hy).mdifferentiableAt
    one_ne_zero

end Poincare
