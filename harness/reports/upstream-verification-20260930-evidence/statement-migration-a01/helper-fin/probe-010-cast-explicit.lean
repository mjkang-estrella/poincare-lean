import Mathlib.Topology.Subpath
universe u
example {Y : Type u} [TopologicalSpace Y] {U V : Set Y} {x y z : Y}
    (hx : x ∈ U ∩ V) (hy : y ∈ U ∩ V)
    (overlapPath : Path (⟨x, hx⟩ : (U ∩ V : Set Y)) (⟨y, hy⟩ : (U ∩ V : Set Y)))
    (hzx : z = x) : True := by
  let incl : C((U ∩ V : Set Y), Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let r : Path x y := overlapPath.map incl.continuous
  let rBack : Path y z := r.symm.cast rfl hzx
  have hrURange : Set.range r ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact (overlapPath t).2.1
  have hrVRange : Set.range r ⊆ V := by
    rintro _ ⟨t, rfl⟩
    exact (overlapPath t).2.2
  have hrBackURange : Set.range rBack ⊆ U := by
    rintro _ ⟨t, rfl⟩
    simpa only [rBack, Path.cast_coe, Path.symm_coe] using hrURange ⟨unitInterval.symm t, rfl⟩
  have hrBackVRange : Set.range rBack ⊆ V := by
    rintro _ ⟨t, rfl⟩
    simpa only [rBack, Path.cast_coe, Path.symm_coe] using hrVRange ⟨unitInterval.symm t, rfl⟩
  trivial

example {X : Type u} [TopologicalSpace X] {x x' y y' : X}
    (p q : Path x y) (hx : x' = x) (hy : y' = y)
    (hCast : Path.Homotopic (p.cast hx hy) (q.cast hx hy)) :
    Path.Homotopic p q := by
  have hCastBack := Path.Homotopic.pathCast hCast hx.symm hy.symm
  have hpBack : (p.cast hx hy).cast hx.symm hy.symm = p := by
    apply Path.ext
    rfl
  have hqBack : (q.cast hx hy).cast hx.symm hy.symm = q := by
    apply Path.ext
    rfl
  simpa only [hpBack, hqBack] using hCastBack
