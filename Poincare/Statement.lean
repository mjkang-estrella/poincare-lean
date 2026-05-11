/-
Copyright (c) 2026.

This file is a statement-layer scaffold for a future Lean formalization of the
Poincare Conjecture. It deliberately does not claim a proof.

The goal theorem is:

  Every closed, simply connected topological 3-manifold is homeomorphic to S^3.

The declarations below use mathlib's existing topology/manifold vocabulary and
the canonical mathlib statement file `Mathlib.Geometry.Manifold.PoincareConjecture`.
-/

import Mathlib.Geometry.Manifold.PoincareConjecture
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.HomotopyGroup

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The 3-sphere as the unit metric sphere in `ℝ⁴`.

This is the same model used by mathlib's `Geometry.Manifold.PoincareConjecture`
file for `𝕊³`.
-/
abbrev ThreeSphere : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)

/-- The target sphere is the unit metric sphere in four-dimensional Euclidean space. -/
theorem threeSphere_eq :
    ThreeSphere = Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ) :=
  rfl

/-- The target 3-sphere is Hausdorff. -/
theorem threeSphere_t2Space :
    T2Space ThreeSphere :=
  inferInstance

/-- The target 3-sphere Hausdorff witness is the inherited subtype instance. -/
theorem threeSphere_t2Space_eq :
    threeSphere_t2Space = (inferInstance : T2Space ThreeSphere) := by
  apply Subsingleton.elim

/-- The target 3-sphere is compact. -/
theorem threeSphere_compactSpace :
    CompactSpace ThreeSphere :=
  inferInstance

/-- The target 3-sphere compactness witness is mathlib's compact sphere instance. -/
theorem threeSphere_compactSpace_eq :
    threeSphere_compactSpace = (inferInstance : CompactSpace ThreeSphere) := by
  apply Subsingleton.elim

/-- The target 3-sphere carries the expected 3-dimensional charted-space structure. -/
@[reducible] noncomputable def threeSphere_chartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere :=
  inferInstance

/-- The target 3-sphere charted-space structure is mathlib's sphere instance. -/
theorem threeSphere_chartedSpace_eq :
    threeSphere_chartedSpace =
      (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere) :=
  rfl

/-- The target 3-sphere carries the expected smooth manifold structure. -/
theorem threeSphere_smoothManifold :
    IsManifold (𝓡 3) ∞ ThreeSphere :=
  inferInstance

/-- The target 3-sphere smoothness witness is mathlib's sphere manifold instance. -/
theorem threeSphere_smoothManifold_eq :
    threeSphere_smoothManifold =
      (inferInstance : IsManifold (𝓡 3) ∞ ThreeSphere) := by
  apply Subsingleton.elim

/--
The ambient Euclidean space for the project target sphere has rank greater than
one, the input needed by mathlib's connected-sphere theorem.
-/
theorem threeSphere_euclidean_rank_gt_one :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
  rw [(EuclideanSpace.equiv (Fin 4) ℝ).toLinearEquiv.rank_eq]
  rw [rank_fin_fun]
  norm_num

/-- The rank witness is the finite-dimensional rank computation for `ℝ^4`. -/
theorem threeSphere_euclidean_rank_gt_one_eq :
    threeSphere_euclidean_rank_gt_one =
      (by
        rw [(EuclideanSpace.equiv (Fin 4) ℝ).toLinearEquiv.rank_eq]
        rw [rank_fin_fun]
        norm_num) := by
  apply Subsingleton.elim

/-- The target 3-sphere is path-connected as a subset of Euclidean space. -/
theorem threeSphere_isPathConnected_set :
    IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  exact isPathConnected_sphere threeSphere_euclidean_rank_gt_one
    (0 : EuclideanSpace ℝ (Fin 4)) (by norm_num)

/-- The path-connectedness proof is mathlib's connected-sphere theorem. -/
theorem threeSphere_isPathConnected_set_eq :
    threeSphere_isPathConnected_set =
      isPathConnected_sphere threeSphere_euclidean_rank_gt_one
        (0 : EuclideanSpace ℝ (Fin 4)) (by norm_num) := by
  apply Subsingleton.elim

/-- The target 3-sphere type is path-connected. -/
theorem threeSphere_pathConnectedSpace :
    PathConnectedSpace ThreeSphere := by
  exact isPathConnected_iff_pathConnectedSpace.mp threeSphere_isPathConnected_set

/-- The target type's path-connectedness is induced from the ambient sphere. -/
theorem threeSphere_pathConnectedSpace_eq :
    threeSphere_pathConnectedSpace =
      isPathConnected_iff_pathConnectedSpace.mp threeSphere_isPathConnected_set := by
  apply Subsingleton.elim

/-- The target 3-sphere is locally path-connected through its charted-space structure. -/
theorem threeSphere_locPathConnectedSpace :
    LocPathConnectedSpace ThreeSphere := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere := threeSphere_chartedSpace
  exact ChartedSpace.locPathConnectedSpace (H := EuclideanSpace ℝ (Fin 3)) (M := ThreeSphere)

/-- Local path-connectedness follows from the named standard charted-space structure. -/
theorem threeSphere_locPathConnectedSpace_eq :
    threeSphere_locPathConnectedSpace =
      (by
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere := threeSphere_chartedSpace
        exact ChartedSpace.locPathConnectedSpace
          (H := EuclideanSpace ℝ (Fin 3)) (M := ThreeSphere)) := by
  apply Subsingleton.elim

/-- The target 3-sphere type is connected. -/
theorem threeSphere_connectedSpace :
    ConnectedSpace ThreeSphere := by
  letI : PathConnectedSpace ThreeSphere := threeSphere_pathConnectedSpace
  infer_instance

/-- Connectedness follows from the named path-connectedness proof. -/
theorem threeSphere_connectedSpace_eq :
    threeSphere_connectedSpace =
      (by
        letI : PathConnectedSpace ThreeSphere := threeSphere_pathConnectedSpace
        infer_instance) := by
  apply Subsingleton.elim

/-- The target 3-sphere is nonempty. -/
theorem threeSphere_nonempty :
    Nonempty ThreeSphere := by
  letI : PathConnectedSpace ThreeSphere := threeSphere_pathConnectedSpace
  infer_instance

/-- The target 3-sphere nonemptiness witness is induced by path-connectedness. -/
theorem threeSphere_nonempty_eq :
    threeSphere_nonempty =
      (by
        letI : PathConnectedSpace ThreeSphere := threeSphere_pathConnectedSpace
        infer_instance) := by
  apply Subsingleton.elim

/--
All standard-sphere prerequisites currently available locally for applying the
target statement to `ThreeSphere`, excluding the simple-connectedness input.
-/
theorem threeSphere_target_prerequisites_except_simpleConnected :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  exact ⟨threeSphere_t2Space, threeSphere_chartedSpace, threeSphere_compactSpace,
    threeSphere_smoothManifold, threeSphere_pathConnectedSpace,
    threeSphere_connectedSpace, threeSphere_nonempty⟩

/--
The available standard-sphere prerequisite payload is exactly the tuple of the
named local target-sphere witnesses.
-/
theorem threeSphere_target_prerequisites_except_simpleConnected_eq :
    threeSphere_target_prerequisites_except_simpleConnected =
      ⟨threeSphere_t2Space, threeSphere_chartedSpace, threeSphere_compactSpace,
        threeSphere_smoothManifold, threeSphere_pathConnectedSpace,
        threeSphere_connectedSpace, threeSphere_nonempty⟩ := by
  apply Subsingleton.elim

/--
All standard-sphere prerequisites for applying the target statement to
`ThreeSphere`, with the simple-connectedness input kept as an explicit
typeclass assumption.
-/
theorem threeSphere_target_prerequisites [SimplyConnectedSpace ThreeSphere] :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  exact ⟨threeSphere_t2Space, threeSphere_chartedSpace, inferInstance,
    threeSphere_compactSpace, threeSphere_smoothManifold,
    threeSphere_pathConnectedSpace, threeSphere_connectedSpace,
    threeSphere_nonempty⟩

/--
The full standard-sphere prerequisite payload is the named local witness tuple,
with simple-connectedness supplied by the current typeclass context.
-/
theorem threeSphere_target_prerequisites_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_target_prerequisites =
      ⟨threeSphere_t2Space, threeSphere_chartedSpace,
        (inferInstance : SimplyConnectedSpace ThreeSphere),
        threeSphere_compactSpace, threeSphere_smoothManifold,
        threeSphere_pathConnectedSpace, threeSphere_connectedSpace,
        threeSphere_nonempty⟩ := by
  apply Subsingleton.elim

/--
Standard-sphere prerequisites useful for homotopy-level arguments, excluding
the simple-connectedness input.  This extends the target prerequisite payload
with local path-connectedness, which is often required by covering-space and
fundamental-group arguments.
-/
theorem threeSphere_homotopy_prerequisites_except_simpleConnected :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _locPath : LocPathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  exact ⟨threeSphere_t2Space, threeSphere_chartedSpace, threeSphere_compactSpace,
    threeSphere_smoothManifold, threeSphere_pathConnectedSpace,
    threeSphere_locPathConnectedSpace, threeSphere_connectedSpace,
    threeSphere_nonempty⟩

/--
The homotopy prerequisite payload is exactly the tuple of named standard-sphere
facts, still leaving simple-connectedness outside the local proof surface.
-/
theorem threeSphere_homotopy_prerequisites_except_simpleConnected_eq :
    threeSphere_homotopy_prerequisites_except_simpleConnected =
      ⟨threeSphere_t2Space, threeSphere_chartedSpace, threeSphere_compactSpace,
        threeSphere_smoothManifold, threeSphere_pathConnectedSpace,
        threeSphere_locPathConnectedSpace, threeSphere_connectedSpace,
        threeSphere_nonempty⟩ := by
  apply Subsingleton.elim

/--
Full standard-sphere homotopy prerequisites, with simple-connectedness kept as
an explicit typeclass input rather than locally asserted.
-/
theorem threeSphere_homotopy_prerequisites [SimplyConnectedSpace ThreeSphere] :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _locPath : LocPathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  exact ⟨threeSphere_t2Space, threeSphere_chartedSpace, inferInstance,
    threeSphere_compactSpace, threeSphere_smoothManifold,
    threeSphere_pathConnectedSpace, threeSphere_locPathConnectedSpace,
    threeSphere_connectedSpace, threeSphere_nonempty⟩

/--
The full homotopy prerequisite payload is exactly the named standard-sphere
fact tuple, with simple-connectedness supplied by the current typeclass context.
-/
theorem threeSphere_homotopy_prerequisites_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_homotopy_prerequisites =
      ⟨threeSphere_t2Space, threeSphere_chartedSpace,
        (inferInstance : SimplyConnectedSpace ThreeSphere),
        threeSphere_compactSpace, threeSphere_smoothManifold,
        threeSphere_pathConnectedSpace, threeSphere_locPathConnectedSpace,
        threeSphere_connectedSpace, threeSphere_nonempty⟩ := by
  apply Subsingleton.elim

set_option backward.isDefEq.respectTransparency false in
/--
In a path-connected space, it is enough to null-homotope the loops at one
basepoint.  This is the change-of-basepoint reduction used to turn a
fundamental-group computation at a chosen point into the loop formulation of
simple-connectedness.
-/
theorem simplyConnectedSpace_iff_pathConnectedSpace_and_basedLoopNullhomotopy
    {Y : Type u} [TopologicalSpace Y] (basepoint : Y) :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧
        ∀ γ : Path basepoint basepoint,
          Path.Homotopic γ (Path.refl basepoint) := by
  open Path.Homotopic.Quotient in
  constructor
  · intro h
    haveI : SimplyConnectedSpace Y := h
    exact ⟨inferInstance,
      fun γ => SimplyConnectedSpace.paths_homotopic γ (Path.refl basepoint)⟩
  · intro h
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨h.1, ?_⟩
    intro x γ
    rw [← Path.Homotopic.Quotient.eq]
    replace hbase : ∀ γ : Path basepoint basepoint,
        (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint) =
          ⟦Path.refl basepoint⟧ :=
      fun γ => Quotient.sound (h.2 γ)
    letI : PathConnectedSpace Y := h.1
    let p : Path basepoint x := PathConnectedSpace.somePath basepoint x
    have hp :
        Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans ⟦p⟧ ⟦γ⟧)
            (Path.Homotopic.Quotient.symm ⟦p⟧) =
          Path.Homotopic.Quotient.refl basepoint := by
      simpa using hbase ((p.trans γ).trans p.symm)
    calc ⟦γ⟧
      _ =
          Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.symm ⟦p⟧)
              (Path.Homotopic.Quotient.trans
                (Path.Homotopic.Quotient.trans ⟦p⟧ ⟦γ⟧)
                (Path.Homotopic.Quotient.symm ⟦p⟧)))
            ⟦p⟧ := by
        grind
      _ =
          Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.symm ⟦p⟧)
              (Path.Homotopic.Quotient.refl basepoint))
            ⟦p⟧ := by
        rw [hp]
      _ = ⟦Path.refl x⟧ := by
        simp

/--
The based-loop change-of-basepoint criterion exposes simple-connectedness as the
based loop-nullhomotopy payload and reconstructs it with the same named
criterion.
-/
theorem simplyConnectedSpace_iff_pathConnectedSpace_and_basedLoopNullhomotopy_eq
    {Y : Type u} [TopologicalSpace Y] (basepoint : Y) :
    simplyConnectedSpace_iff_pathConnectedSpace_and_basedLoopNullhomotopy basepoint =
      ⟨fun h =>
          letI : SimplyConnectedSpace Y := h
          ⟨inferInstance,
            fun γ => SimplyConnectedSpace.paths_homotopic γ (Path.refl basepoint)⟩,
        fun h =>
          (simplyConnectedSpace_iff_pathConnectedSpace_and_basedLoopNullhomotopy
            basepoint).mpr h⟩ := by
  apply Subsingleton.elim

/--
The based loop-nullhomotopy obligation for the standard 3-sphere at a chosen
basepoint.
-/
def ThreeSphereBasedLoopNullhomotopyStatement (basepoint : ThreeSphere) : Prop :=
  ∀ γ : Path basepoint basepoint, Path.Homotopic γ (Path.refl basepoint)

/-- The based loop-nullhomotopy obligation expands to nullhomotopy at the chosen basepoint. -/
theorem threeSphereBasedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    ThreeSphereBasedLoopNullhomotopyStatement basepoint =
      (∀ γ : Path basepoint basepoint, Path.Homotopic γ (Path.refl basepoint)) :=
  rfl

/--
For the standard sphere, simple-connectedness is equivalent to nullhomotopy of
all loops at any chosen basepoint, because path-connectedness has already been
proved.
-/
theorem threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement
    (basepoint : ThreeSphere) :
    SimplyConnectedSpace ThreeSphere ↔
      ThreeSphereBasedLoopNullhomotopyStatement basepoint := by
  rw [threeSphereBasedLoopNullhomotopyStatement_eq]
  exact
    ⟨fun h =>
        ((simplyConnectedSpace_iff_pathConnectedSpace_and_basedLoopNullhomotopy
          basepoint).mp h).2,
      fun h =>
        (simplyConnectedSpace_iff_pathConnectedSpace_and_basedLoopNullhomotopy
          basepoint).mpr ⟨threeSphere_pathConnectedSpace, h⟩⟩

/--
The based-loop simple-connectedness reduction is the general change-of-basepoint
criterion specialized with the named path-connectedness proof for `S^3`.
-/
theorem threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement basepoint =
      ⟨fun h =>
          ((simplyConnectedSpace_iff_pathConnectedSpace_and_basedLoopNullhomotopy
            basepoint).mp h).2,
        fun h =>
          (simplyConnectedSpace_iff_pathConnectedSpace_and_basedLoopNullhomotopy
            basepoint).mpr ⟨threeSphere_pathConnectedSpace, h⟩⟩ := by
  apply Subsingleton.elim

/-- A based loop-nullhomotopy proof supplies simple-connectedness of `S^3`. -/
theorem threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (h : ThreeSphereBasedLoopNullhomotopyStatement basepoint) :
    SimplyConnectedSpace ThreeSphere :=
  (threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement
    basepoint).mpr h

/-- The based-loop-to-simple-connectedness route is the reverse reduction projection. -/
theorem threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h) =
      (threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement
        basepoint).mpr := by
  funext h
  apply Subsingleton.elim

/-- A supplied simple-connectedness instance gives based loop-nullhomotopy at any basepoint. -/
theorem threeSphere_basedLoopNullhomotopyStatement_of_simplyConnectedSpace
    (basepoint : ThreeSphere) [SimplyConnectedSpace ThreeSphere] :
    ThreeSphereBasedLoopNullhomotopyStatement basepoint :=
  (threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement
    basepoint).mp inferInstance

/--
The simple-connectedness-to-based-loop route is the forward projection of the
named based-loop criterion.
-/
theorem threeSphere_basedLoopNullhomotopyStatement_of_simplyConnectedSpace_eq
    (basepoint : ThreeSphere) [SimplyConnectedSpace ThreeSphere] :
    threeSphere_basedLoopNullhomotopyStatement_of_simplyConnectedSpace basepoint =
      (threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement
        basepoint).mp inferInstance := by
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation whose proof would supply
`SimplyConnectedSpace ThreeSphere`.
-/
def ThreeSphereLoopNullhomotopyStatement : Prop :=
  ∀ (x : ThreeSphere) (γ : Path x x), Path.Homotopic γ (Path.refl x)

/-- The loop-nullhomotopy obligation expands to nullhomotopy of every based loop. -/
theorem threeSphereLoopNullhomotopyStatement_eq :
    ThreeSphereLoopNullhomotopyStatement =
      (∀ (x : ThreeSphere) (γ : Path x x), Path.Homotopic γ (Path.refl x)) :=
  rfl

/--
For the standard sphere, simple-connectedness is equivalent to the concrete
loop-nullhomotopy obligation because path-connectedness has already been proved.
-/
theorem threeSphere_simplyConnectedSpace_iff_loopNullhomotopyStatement :
    SimplyConnectedSpace ThreeSphere ↔ ThreeSphereLoopNullhomotopyStatement := by
  rw [threeSphereLoopNullhomotopyStatement_eq,
    simply_connected_iff_loops_nullhomotopic]
  exact ⟨fun h => h.2, fun h => ⟨threeSphere_pathConnectedSpace, h⟩⟩

/--
The simple-connectedness reduction is exactly mathlib's loop-nullhomotopy
criterion specialized with the named path-connectedness proof for `S^3`.
-/
theorem threeSphere_simplyConnectedSpace_iff_loopNullhomotopyStatement_eq :
    threeSphere_simplyConnectedSpace_iff_loopNullhomotopyStatement =
      (by
        rw [threeSphereLoopNullhomotopyStatement_eq,
          simply_connected_iff_loops_nullhomotopic]
        exact ⟨fun h => h.2,
          fun h => ⟨threeSphere_pathConnectedSpace, h⟩⟩) := by
  apply Subsingleton.elim

/-- A proof of the loop-nullhomotopy obligation supplies simple-connectedness of `S^3`. -/
theorem threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement
    (h : ThreeSphereLoopNullhomotopyStatement) :
    SimplyConnectedSpace ThreeSphere :=
  threeSphere_simplyConnectedSpace_iff_loopNullhomotopyStatement.mpr h

/-- The loop-nullhomotopy-to-simple-connectedness route is the forward reduction projection. -/
theorem threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement_eq :
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement =
      threeSphere_simplyConnectedSpace_iff_loopNullhomotopyStatement.mpr := by
  funext h
  apply Subsingleton.elim

/-- A supplied simple-connectedness instance gives the concrete loop-nullhomotopy obligation. -/
theorem threeSphere_loopNullhomotopyStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace ThreeSphere] :
    ThreeSphereLoopNullhomotopyStatement :=
  threeSphere_simplyConnectedSpace_iff_loopNullhomotopyStatement.mp inferInstance

/--
The simple-connectedness-to-loop-nullhomotopy route is the reverse reduction
projection.
-/
theorem threeSphere_loopNullhomotopyStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_loopNullhomotopyStatement_of_simplyConnectedSpace =
      threeSphere_simplyConnectedSpace_iff_loopNullhomotopyStatement.mp inferInstance := by
  apply Subsingleton.elim

/--
Based loop-nullhomotopy at one chosen point supplies the full loop-nullhomotopy
obligation for `S^3`.
-/
theorem threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (h : ThreeSphereBasedLoopNullhomotopyStatement basepoint) :
    ThreeSphereLoopNullhomotopyStatement := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h
  exact threeSphere_loopNullhomotopyStatement_of_simplyConnectedSpace

/--
The based-loop-to-full-loop route is simple-connectedness from the based loop
criterion followed by the full loop criterion.
-/
theorem threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h
        threeSphere_loopNullhomotopyStatement_of_simplyConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/--
The concrete path-homotopy uniqueness obligation whose proof would also supply
`SimplyConnectedSpace ThreeSphere`.
-/
def ThreeSpherePathHomotopyStatement : Prop :=
  ∀ {x y : ThreeSphere} (p q : Path x y), Path.Homotopic p q

/-- The path-homotopy obligation expands to homotopy of every parallel path pair. -/
theorem threeSpherePathHomotopyStatement_eq :
    ThreeSpherePathHomotopyStatement =
      (∀ {x y : ThreeSphere} (p q : Path x y), Path.Homotopic p q) :=
  rfl

/--
For the standard sphere, simple-connectedness is equivalent to the concrete
path-homotopy obligation because path-connectedness has already been proved.
-/
theorem threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement :
    SimplyConnectedSpace ThreeSphere ↔ ThreeSpherePathHomotopyStatement := by
  rw [threeSpherePathHomotopyStatement_eq,
    simply_connected_iff_paths_homotopic']
  exact ⟨fun h => h.2, fun h => ⟨threeSphere_pathConnectedSpace, h⟩⟩

/--
The simple-connectedness/path-homotopy reduction is exactly mathlib's
path-homotopy criterion specialized with the named path-connectedness proof.
-/
theorem threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement_eq :
    threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement =
      (by
        rw [threeSpherePathHomotopyStatement_eq,
          simply_connected_iff_paths_homotopic']
        exact ⟨fun h => h.2,
          fun h => ⟨threeSphere_pathConnectedSpace, h⟩⟩) := by
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation directly supplies simple-connectedness
for the standard sphere.
-/
theorem threeSphere_simplyConnectedSpace_of_pathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    SimplyConnectedSpace ThreeSphere :=
  threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement.mpr h

/--
The path-homotopy-to-simple-connectedness route is exactly the reverse
direction of the named path-homotopy criterion.
-/
theorem threeSphere_simplyConnectedSpace_of_pathHomotopyStatement_eq :
    threeSphere_simplyConnectedSpace_of_pathHomotopyStatement =
      threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement.mpr := by
  funext h
  apply Subsingleton.elim

/--
Simple-connectedness directly supplies the concrete path-homotopy obligation
for the standard sphere.
-/
theorem threeSphere_pathHomotopyStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace ThreeSphere] :
    ThreeSpherePathHomotopyStatement :=
  threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement.mp inferInstance

/--
The simple-connectedness-to-path-homotopy route is exactly the forward direction
of the named path-homotopy criterion.
-/
theorem threeSphere_pathHomotopyStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace ThreeSphere] :
    (threeSphere_pathHomotopyStatement_of_simplyConnectedSpace :
      ThreeSpherePathHomotopyStatement) =
      (threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement.mp inferInstance :
        ThreeSpherePathHomotopyStatement) := by
  apply Subsingleton.elim

/-- Path-homotopy uniqueness implies loop-nullhomotopy by comparing a loop to `Path.refl`. -/
theorem threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    ThreeSphereLoopNullhomotopyStatement := by
  intro x γ
  exact h γ (Path.refl x)

/-- The path-to-loop route is evaluation at a loop and the stationary loop. -/
theorem threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement_eq :
    threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        fun x γ => h γ (Path.refl x)) := by
  funext h x γ
  apply Subsingleton.elim

/-- Loop-nullhomotopy implies path-homotopy uniqueness through simple-connectedness. -/
theorem threeSphere_pathHomotopyStatement_of_loopNullhomotopyStatement
    (h : ThreeSphereLoopNullhomotopyStatement) :
    ThreeSpherePathHomotopyStatement :=
  threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement.mp
    (threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h)

/--
The loop-to-path route is simple-connectedness from loop-nullhomotopy followed
by the path-homotopy criterion.
-/
theorem threeSphere_pathHomotopyStatement_of_loopNullhomotopyStatement_eq :
    threeSphere_pathHomotopyStatement_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        (threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement.mp
          (threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h) :
            ThreeSpherePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- The two concrete simple-connectedness obligations for `S^3` are equivalent. -/
theorem threeSphere_pathHomotopyStatement_iff_loopNullhomotopyStatement :
    ThreeSpherePathHomotopyStatement ↔ ThreeSphereLoopNullhomotopyStatement :=
  ⟨threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement,
    threeSphere_pathHomotopyStatement_of_loopNullhomotopyStatement⟩

/--
The path/loop obligation equivalence is exactly the pair of named conversion
routes.
-/
theorem threeSphere_pathHomotopyStatement_iff_loopNullhomotopyStatement_eq :
    threeSphere_pathHomotopyStatement_iff_loopNullhomotopyStatement =
      ⟨threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement,
        threeSphere_pathHomotopyStatement_of_loopNullhomotopyStatement⟩ := by
  apply Subsingleton.elim

/--
The fundamental-groupoid quotient uniqueness obligation whose proof would also
supply `SimplyConnectedSpace ThreeSphere`.
-/
def ThreeSpherePathQuotientSubsingletonStatement : Prop :=
  ∀ x y : ThreeSphere, Subsingleton (Path.Homotopic.Quotient x y)

/--
The quotient uniqueness obligation expands to subsingleton path-homotopy
quotients between every pair of points in the standard sphere.
-/
theorem threeSpherePathQuotientSubsingletonStatement_eq :
    ThreeSpherePathQuotientSubsingletonStatement =
      (∀ x y : ThreeSphere, Subsingleton (Path.Homotopic.Quotient x y)) :=
  rfl

/--
For the standard sphere, simple-connectedness is equivalent to uniqueness of
path-homotopy quotients because path-connectedness has already been proved.
-/
theorem threeSphere_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement :
    SimplyConnectedSpace ThreeSphere ↔
      ThreeSpherePathQuotientSubsingletonStatement := by
  rw [threeSpherePathQuotientSubsingletonStatement_eq,
    simply_connected_iff_paths_homotopic]
  exact ⟨fun h => h.2, fun h => ⟨threeSphere_pathConnectedSpace, h⟩⟩

/--
The simple-connectedness/path-quotient reduction is exactly mathlib's
path-homotopy quotient criterion specialized with the named path-connectedness
proof.
-/
theorem threeSphere_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement_eq :
    threeSphere_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement =
      (by
        rw [threeSpherePathQuotientSubsingletonStatement_eq,
          simply_connected_iff_paths_homotopic]
        exact ⟨fun h => h.2,
          fun h => ⟨threeSphere_pathConnectedSpace, h⟩⟩) := by
  apply Subsingleton.elim

/--
The quotient uniqueness obligation directly supplies simple-connectedness for
the standard sphere.
-/
theorem threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement
    (h : ThreeSpherePathQuotientSubsingletonStatement) :
    SimplyConnectedSpace ThreeSphere :=
  threeSphere_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mpr h

/--
The quotient-uniqueness-to-simple-connectedness route is exactly the reverse
direction of the named quotient criterion.
-/
theorem threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement_eq :
    threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement =
      threeSphere_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mpr := by
  funext h
  apply Subsingleton.elim

/--
Simple-connectedness directly supplies quotient uniqueness for every
path-homotopy quotient on the standard sphere.
-/
theorem threeSphere_pathQuotientSubsingletonStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace ThreeSphere] :
    ThreeSpherePathQuotientSubsingletonStatement :=
  threeSphere_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mp
    inferInstance

/--
The simple-connectedness-to-quotient-uniqueness route is exactly the forward
direction of the named quotient criterion.
-/
theorem threeSphere_pathQuotientSubsingletonStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace ThreeSphere] :
    (threeSphere_pathQuotientSubsingletonStatement_of_simplyConnectedSpace :
      ThreeSpherePathQuotientSubsingletonStatement) =
      (threeSphere_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mp
        inferInstance : ThreeSpherePathQuotientSubsingletonStatement) := by
  apply Subsingleton.elim

/--
Path-homotopy uniqueness gives quotient uniqueness through the named
simple-connectedness criterion.
-/
theorem threeSphere_pathQuotientSubsingletonStatement_of_pathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    ThreeSpherePathQuotientSubsingletonStatement :=
  threeSphere_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mp
    (threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h)

/--
The path-homotopy-to-quotient route is simple-connectedness from path-homotopy
followed by the quotient criterion.
-/
theorem threeSphere_pathQuotientSubsingletonStatement_of_pathHomotopyStatement_eq :
    threeSphere_pathQuotientSubsingletonStatement_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        (threeSphere_simplyConnectedSpace_iff_pathQuotientSubsingletonStatement.mp
          (threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h) :
            ThreeSpherePathQuotientSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/--
Quotient uniqueness gives path-homotopy uniqueness through the named
simple-connectedness criterion.
-/
theorem threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement
    (h : ThreeSpherePathQuotientSubsingletonStatement) :
    ThreeSpherePathHomotopyStatement :=
  threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement.mp
    (threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h)

/--
The quotient-to-path route is simple-connectedness from quotient uniqueness
followed by the path-homotopy criterion.
-/
theorem threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement_eq :
    threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        (threeSphere_simplyConnectedSpace_iff_pathHomotopyStatement.mp
          (threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h) :
            ThreeSpherePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/--
The path-homotopy and path-quotient formulations of the standard-sphere
simple-connectedness obligation are equivalent.
-/
theorem threeSphere_pathHomotopyStatement_iff_pathQuotientSubsingletonStatement :
    ThreeSpherePathHomotopyStatement ↔
      ThreeSpherePathQuotientSubsingletonStatement :=
  ⟨threeSphere_pathQuotientSubsingletonStatement_of_pathHomotopyStatement,
    threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement⟩

/--
The path-homotopy/path-quotient equivalence is exactly the pair of named
conversion routes.
-/
theorem threeSphere_pathHomotopyStatement_iff_pathQuotientSubsingletonStatement_eq :
    threeSphere_pathHomotopyStatement_iff_pathQuotientSubsingletonStatement =
      ⟨threeSphere_pathQuotientSubsingletonStatement_of_pathHomotopyStatement,
        threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement⟩ := by
  apply Subsingleton.elim

/--
The fundamental-group formulation of the remaining simple-connectedness
obligation for the standard 3-sphere: every based fundamental group is trivial
as a type.
-/
def ThreeSphereFundamentalGroupSubsingletonStatement : Prop :=
  ∀ x : ThreeSphere, Subsingleton (FundamentalGroup ThreeSphere x)

/--
The fundamental-group obligation expands to subsingleton fundamental groups at
every basepoint.
-/
theorem threeSphereFundamentalGroupSubsingletonStatement_eq :
    ThreeSphereFundamentalGroupSubsingletonStatement =
      (∀ x : ThreeSphere, Subsingleton (FundamentalGroup ThreeSphere x)) :=
  rfl

/--
Simple-connectedness of the standard sphere gives the fundamental-group
subsingleton obligation at every basepoint.
-/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace ThreeSphere] :
    ThreeSphereFundamentalGroupSubsingletonStatement := by
  intro x
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/-- The simple-connectedness-to-fundamental-group route is quotient uniqueness for loops. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_fundamentalGroupSubsingletonStatement_of_simplyConnectedSpace =
      (by
        intro x
        change Subsingleton (Path.Homotopic.Quotient x x)
        infer_instance) := by
  apply Subsingleton.elim

/--
Loop-nullhomotopy of every based loop gives the fundamental-group subsingleton
obligation through the simple-connectedness criterion.
-/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement
    (h : ThreeSphereLoopNullhomotopyStatement) :
    ThreeSphereFundamentalGroupSubsingletonStatement := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
  exact threeSphere_fundamentalGroupSubsingletonStatement_of_simplyConnectedSpace

/--
The loop-nullhomotopy-to-fundamental-group route factors through the named
simple-connectedness reduction.
-/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement_eq :
    threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
        threeSphere_fundamentalGroupSubsingletonStatement_of_simplyConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/--
Fundamental-group triviality gives loop-nullhomotopy: every loop quotient is
equal to the quotient of the stationary loop.
-/
theorem threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
    (h : ThreeSphereFundamentalGroupSubsingletonStatement) :
    ThreeSphereLoopNullhomotopyStatement := by
  intro x γ
  rw [← Path.Homotopic.Quotient.eq]
  exact (h x).elim (⟦γ⟧ : Path.Homotopic.Quotient x x)
    ⟦Path.refl x⟧

/-- The fundamental-group-to-loop route is quotient subsingleton elimination. -/
theorem threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement =
      (fun h : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun x γ =>
          by
            rw [← Path.Homotopic.Quotient.eq]
            exact (h x).elim (⟦γ⟧ : Path.Homotopic.Quotient x x)
              ⟦Path.refl x⟧) := by
  funext h x γ
  apply Subsingleton.elim

/--
The fundamental-group and loop-nullhomotopy formulations of the standard
sphere simple-connectedness obligation are equivalent.
-/
theorem threeSphere_fundamentalGroupSubsingletonStatement_iff_loopNullhomotopyStatement :
    ThreeSphereFundamentalGroupSubsingletonStatement ↔
      ThreeSphereLoopNullhomotopyStatement :=
  ⟨threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement,
    threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement⟩

/-- The fundamental-group/loop equivalence is the pair of named conversion routes. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_iff_loopNullhomotopyStatement_eq :
    threeSphere_fundamentalGroupSubsingletonStatement_iff_loopNullhomotopyStatement =
      ⟨threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement,
        threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement⟩ := by
  apply Subsingleton.elim

/--
The standard sphere is simply connected exactly when all of its based
fundamental groups are subsingletons.
-/
theorem threeSphere_simplyConnectedSpace_iff_fundamentalGroupSubsingletonStatement :
    SimplyConnectedSpace ThreeSphere ↔
      ThreeSphereFundamentalGroupSubsingletonStatement := by
  exact threeSphere_simplyConnectedSpace_iff_loopNullhomotopyStatement.trans
    threeSphere_fundamentalGroupSubsingletonStatement_iff_loopNullhomotopyStatement.symm

/--
The simple-connectedness/fundamental-group reduction factors through the
existing loop-nullhomotopy criterion.
-/
theorem threeSphere_simplyConnectedSpace_iff_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_simplyConnectedSpace_iff_fundamentalGroupSubsingletonStatement =
      threeSphere_simplyConnectedSpace_iff_loopNullhomotopyStatement.trans
        threeSphere_fundamentalGroupSubsingletonStatement_iff_loopNullhomotopyStatement.symm := by
  apply Subsingleton.elim

/--
Fundamental-group triviality supplies simple-connectedness of the standard
3-sphere.
-/
theorem threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement
    (h : ThreeSphereFundamentalGroupSubsingletonStatement) :
    SimplyConnectedSpace ThreeSphere :=
  threeSphere_simplyConnectedSpace_iff_fundamentalGroupSubsingletonStatement.mpr h

/-- The fundamental-group-to-simple-connectedness route is the reverse criterion projection. -/
theorem threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement =
      threeSphere_simplyConnectedSpace_iff_fundamentalGroupSubsingletonStatement.mpr := by
  funext h
  apply Subsingleton.elim

/--
The first-homotopy-group formulation of the remaining simple-connectedness
obligation for the standard 3-sphere.
-/
def ThreeSpherePiOneSubsingletonStatement : Prop :=
  ∀ x : ThreeSphere, Subsingleton (HomotopyGroup.Pi 1 ThreeSphere x)

/-- The `π₁` obligation expands to subsingleton first homotopy groups at every basepoint. -/
theorem threeSpherePiOneSubsingletonStatement_eq :
    ThreeSpherePiOneSubsingletonStatement =
      (∀ x : ThreeSphere, Subsingleton (HomotopyGroup.Pi 1 ThreeSphere x)) :=
  rfl

/--
The `π₁` and fundamental-group formulations are equivalent through mathlib's
`π₁`/fundamental-group equivalence.
-/
theorem threeSphere_piOneSubsingletonStatement_iff_fundamentalGroupSubsingletonStatement :
    ThreeSpherePiOneSubsingletonStatement ↔
      ThreeSphereFundamentalGroupSubsingletonStatement := by
  constructor
  · intro h x
    exact ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := ThreeSphere) (x := x)).subsingleton_congr).mp (h x)
  · intro h x
    exact ((HomotopyGroup.pi1EquivFundamentalGroup
      (X := ThreeSphere) (x := x)).subsingleton_congr).mpr (h x)

/-- The `π₁`/fundamental-group equivalence is pointwise mathlib's `pi1EquivFundamentalGroup`. -/
theorem threeSphere_piOneSubsingletonStatement_iff_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_piOneSubsingletonStatement_iff_fundamentalGroupSubsingletonStatement =
      (by
        constructor
        · intro h x
          exact ((HomotopyGroup.pi1EquivFundamentalGroup
            (X := ThreeSphere) (x := x)).subsingleton_congr).mp (h x)
        · intro h x
          exact ((HomotopyGroup.pi1EquivFundamentalGroup
            (X := ThreeSphere) (x := x)).subsingleton_congr).mpr (h x)) := by
  apply Subsingleton.elim

/--
The standard sphere is simply connected exactly when all of its first homotopy
groups are subsingletons.
-/
theorem threeSphere_simplyConnectedSpace_iff_piOneSubsingletonStatement :
    SimplyConnectedSpace ThreeSphere ↔
      ThreeSpherePiOneSubsingletonStatement :=
  threeSphere_simplyConnectedSpace_iff_fundamentalGroupSubsingletonStatement.trans
    threeSphere_piOneSubsingletonStatement_iff_fundamentalGroupSubsingletonStatement.symm

/-- The simple-connectedness/`π₁` reduction factors through the fundamental-group endpoint. -/
theorem threeSphere_simplyConnectedSpace_iff_piOneSubsingletonStatement_eq :
    threeSphere_simplyConnectedSpace_iff_piOneSubsingletonStatement =
      threeSphere_simplyConnectedSpace_iff_fundamentalGroupSubsingletonStatement.trans
        threeSphere_piOneSubsingletonStatement_iff_fundamentalGroupSubsingletonStatement.symm := by
  apply Subsingleton.elim

/-- A proof that all `π₁(S^3, x)` are subsingletons supplies simple-connectedness of `S^3`. -/
theorem threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement
    (h : ThreeSpherePiOneSubsingletonStatement) :
    SimplyConnectedSpace ThreeSphere :=
  threeSphere_simplyConnectedSpace_iff_piOneSubsingletonStatement.mpr h

/-- The `π₁`-to-simple-connectedness route is the reverse criterion projection. -/
theorem threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement_eq :
    threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement =
      threeSphere_simplyConnectedSpace_iff_piOneSubsingletonStatement.mpr := by
  funext h
  apply Subsingleton.elim

/-- Simple-connectedness of `S^3` supplies the `π₁` subsingleton formulation. -/
theorem threeSphere_piOneSubsingletonStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace ThreeSphere] :
    ThreeSpherePiOneSubsingletonStatement :=
  threeSphere_simplyConnectedSpace_iff_piOneSubsingletonStatement.mp inferInstance

/-- The simple-connectedness-to-`π₁` route is the forward criterion projection. -/
theorem threeSphere_piOneSubsingletonStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_piOneSubsingletonStatement_of_simplyConnectedSpace =
      threeSphere_simplyConnectedSpace_iff_piOneSubsingletonStatement.mp inferInstance := by
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation supplies the full target prerequisite
payload for applying the project statement to the standard sphere.
-/
theorem threeSphere_target_prerequisites_of_loopNullhomotopyStatement
    (h : ThreeSphereLoopNullhomotopyStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
  exact threeSphere_target_prerequisites

/--
The loop-nullhomotopy target-prerequisite route is exactly the full target
payload after converting loop-nullhomotopy to simple-connectedness.
-/
theorem threeSphere_target_prerequisites_of_loopNullhomotopyStatement_eq :
    threeSphere_target_prerequisites_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
        threeSphere_target_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation also supplies the full
homotopy-oriented prerequisite payload for the standard sphere.
-/
theorem threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement
    (h : ThreeSphereLoopNullhomotopyStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _locPath : LocPathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
  exact threeSphere_homotopy_prerequisites

/--
The loop-nullhomotopy homotopy-prerequisite route is exactly the full homotopy
payload after converting loop-nullhomotopy to simple-connectedness.
-/
theorem threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement_eq :
    threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
        threeSphere_homotopy_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The based loop-nullhomotopy obligation supplies the full target prerequisite
payload for applying the project statement to the standard sphere.
-/
theorem threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (h : ThreeSphereBasedLoopNullhomotopyStatement basepoint) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h
  exact threeSphere_target_prerequisites

/--
The based-loop target-prerequisite route is exactly the full target payload
after converting based loop-nullhomotopy to simple-connectedness.
-/
theorem threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h
        threeSphere_target_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The based loop-nullhomotopy obligation also supplies the full homotopy-oriented
prerequisite payload for the standard sphere.
-/
theorem threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (h : ThreeSphereBasedLoopNullhomotopyStatement basepoint) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _locPath : LocPathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h
  exact threeSphere_homotopy_prerequisites

/--
The based-loop homotopy-prerequisite route is exactly the full homotopy payload
after converting based loop-nullhomotopy to simple-connectedness.
-/
theorem threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h
        threeSphere_homotopy_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The direct based-loop target-prerequisite route agrees with the route that
first expands based loop-nullhomotopy to the full loop obligation.
-/
theorem threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement_loop_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_target_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The direct based-loop homotopy-prerequisite route agrees with the route that
first expands based loop-nullhomotopy to the full loop obligation.
-/
theorem threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement_loop_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation supplies the full target prerequisite
payload by converting path-homotopy directly to simple-connectedness.
-/
theorem threeSphere_target_prerequisites_of_pathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
  exact threeSphere_target_prerequisites

/--
The path-homotopy target-prerequisite route is exactly the full target payload
after converting path-homotopy to simple-connectedness.
-/
theorem threeSphere_target_prerequisites_of_pathHomotopyStatement_eq :
    threeSphere_target_prerequisites_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
        threeSphere_target_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The direct path-homotopy target-prerequisite route agrees with the route that
first converts path-homotopy to loop-nullhomotopy.
-/
theorem threeSphere_target_prerequisites_of_pathHomotopyStatement_loop_route_eq :
    threeSphere_target_prerequisites_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        threeSphere_target_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation supplies the full homotopy-oriented
prerequisite payload by converting path-homotopy directly to
simple-connectedness.
-/
theorem threeSphere_homotopy_prerequisites_of_pathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _locPath : LocPathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
  exact threeSphere_homotopy_prerequisites

/--
The path-homotopy homotopy-prerequisite route is exactly the full homotopy
payload after converting path-homotopy to simple-connectedness.
-/
theorem threeSphere_homotopy_prerequisites_of_pathHomotopyStatement_eq :
    threeSphere_homotopy_prerequisites_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
        threeSphere_homotopy_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The direct path-homotopy homotopy-prerequisite route agrees with the route that
first converts path-homotopy to loop-nullhomotopy.
-/
theorem threeSphere_homotopy_prerequisites_of_pathHomotopyStatement_loop_route_eq :
    threeSphere_homotopy_prerequisites_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The path-quotient uniqueness obligation supplies the full target prerequisite
payload by converting quotient uniqueness to simple-connectedness.
-/
theorem threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement
    (h : ThreeSpherePathQuotientSubsingletonStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
  exact threeSphere_target_prerequisites

/--
The quotient-uniqueness target-prerequisite route is exactly the full target
payload after converting quotient uniqueness to simple-connectedness.
-/
theorem threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement_eq :
    threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
        threeSphere_target_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The quotient-uniqueness target-prerequisite route agrees with the route that
first converts quotient uniqueness to path-homotopy uniqueness.
-/
theorem threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement_path_route_eq :
    threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        threeSphere_target_prerequisites_of_pathHomotopyStatement
          (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The quotient-uniqueness target-prerequisite route also agrees with the route
that first converts quotient uniqueness through path-homotopy uniqueness and
then to loop-nullhomotopy.
-/
theorem threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement_loop_route_eq :
    threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        threeSphere_target_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h))) := by
  funext h
  apply Subsingleton.elim

/--
The path-quotient uniqueness obligation supplies the full homotopy-oriented
prerequisite payload by converting quotient uniqueness to simple-connectedness.
-/
theorem threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement
    (h : ThreeSpherePathQuotientSubsingletonStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _locPath : LocPathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
  exact threeSphere_homotopy_prerequisites

/--
The quotient-uniqueness homotopy-prerequisite route is exactly the full
homotopy payload after converting quotient uniqueness to simple-connectedness.
-/
theorem threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement_eq :
    threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
        threeSphere_homotopy_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The quotient-uniqueness homotopy-prerequisite route agrees with the route that
first converts quotient uniqueness to path-homotopy uniqueness.
-/
theorem threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement_path_route_eq :
    threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        threeSphere_homotopy_prerequisites_of_pathHomotopyStatement
          (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The quotient-uniqueness homotopy-prerequisite route also agrees with the route
that first converts quotient uniqueness through path-homotopy uniqueness and
then to loop-nullhomotopy.
-/
theorem threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement_loop_route_eq :
    threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h))) := by
  funext h
  apply Subsingleton.elim

/--
The actual target statement of the Poincare Conjecture for this project.

This is a proposition only. It is intentionally not declared as a theorem or
proved fact. It mirrors mathlib's existing
proof-wanted topological 3-dimensional Poincare statement without depending on
that declaration.
-/
def PoincareConjectureStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ ThreeSphere)

/-- The target statement expands to the expected topological 3-sphere statement. -/
theorem poincareConjectureStatement_eq :
    PoincareConjectureStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :=
  rfl

/--
The target statement is logically equivalent to the canonical topological
3-sphere statement shape.
-/
theorem poincareConjectureStatement_iff_canonical_three_sphere_statement :
    PoincareConjectureStatement.{u} ↔
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₜ ThreeSphere)) :=
  Iff.rfl

/--
The smooth 3-dimensional Poincare statement, also already represented in
mathlib's canonical statement file as a proof-wanted declaration.
-/
def SmoothPoincareConjectureStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)

/-- The smooth target expands to the expected smooth 3-sphere statement. -/
theorem smoothPoincareConjectureStatement_eq :
    SmoothPoincareConjectureStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :=
  rfl

/--
The smooth target statement is logically equivalent to the canonical smooth
3-sphere statement shape.
-/
theorem smoothPoincareConjectureStatement_iff_canonical_smooth_three_sphere_statement :
    SmoothPoincareConjectureStatement.{u} ↔
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :=
  Iff.rfl

/--
The project is complete only if there is a proof of the target statement.

At present this is just a proposition. There is no proof term here.
-/
def CompletionCriterionAtUniverse (_witness : Type u) : Prop :=
  PoincareConjectureStatement.{u}

/-- The universe-indexed completion criterion is exactly the target statement. -/
theorem completionCriterionAtUniverse_eq (witness : Type u) :
    CompletionCriterionAtUniverse witness = PoincareConjectureStatement.{u} :=
  rfl

/--
The explicit universe-indexed completion criterion is logically equivalent to
the project target statement.
-/
theorem completionCriterionAtUniverse_iff_poincareConjectureStatement
    (witness : Type u) :
    CompletionCriterionAtUniverse witness ↔ PoincareConjectureStatement.{u} :=
  Iff.rfl

/--
The universe-indexed completion criterion is independent of the chosen witness
type.
-/
theorem completionCriterionAtUniverse_of_completionCriterionAtUniverse
    (source target : Type u)
    (h : CompletionCriterionAtUniverse source) :
    CompletionCriterionAtUniverse target :=
  h

/--
Any two witness-indexed completion criteria are logically equivalent.
-/
theorem completionCriterionAtUniverse_iff_completionCriterionAtUniverse
    (source target : Type u) :
    CompletionCriterionAtUniverse source ↔ CompletionCriterionAtUniverse target :=
  Iff.rfl

/-- A proof of the target statement discharges the universe-indexed criterion. -/
theorem completionCriterionAtUniverse_of_poincareConjectureStatement
    (witness : Type u) (h : PoincareConjectureStatement.{u}) :
    CompletionCriterionAtUniverse witness :=
  h

/--
A proof of the target statement exposes the target and the explicit
universe-indexed completion criterion as one payload.
-/
theorem poincare_completion_payload_of_poincareConjectureStatement
    (h : PoincareConjectureStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  exact ⟨h, fun witness =>
    completionCriterionAtUniverse_of_poincareConjectureStatement witness h⟩

/--
The project completion payload contains a proof of the target Poincare
statement.
-/
theorem poincareConjectureStatement_of_poincare_completion_payload
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    PoincareConjectureStatement.{u} := by
  rcases payload with ⟨target, _criterion⟩
  exact target

/--
The project completion payload discharges the explicit universe-indexed
completion criterion.
-/
theorem completionCriterionAtUniverse_of_poincare_completion_payload
    (witness : Type u)
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    CompletionCriterionAtUniverse witness := by
  rcases payload with ⟨_target, criterion⟩
  exact criterion witness

/--
The target Poincare statement is equivalent to the project completion payload.
-/
theorem poincareConjectureStatement_iff_poincare_completion_payload :
    PoincareConjectureStatement.{u} ↔
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  ⟨poincare_completion_payload_of_poincareConjectureStatement,
    poincareConjectureStatement_of_poincare_completion_payload⟩

/-- A proof of the universe-indexed criterion gives the target statement. -/
theorem poincareConjectureStatement_of_completionCriterionAtUniverse
    (witness : Type u) (h : CompletionCriterionAtUniverse witness) :
    PoincareConjectureStatement.{u} :=
  h

/--
A witness-indexed completion criterion exposes the project completion payload.
-/
theorem poincare_completion_payload_of_completionCriterionAtUniverse
    (witness : Type u) (h : CompletionCriterionAtUniverse witness) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincare_completion_payload_of_poincareConjectureStatement
    (poincareConjectureStatement_of_completionCriterionAtUniverse witness h)

/--
The explicit universe-indexed completion criterion is equivalent to the project
completion payload.
-/
theorem completionCriterionAtUniverse_iff_poincare_completion_payload
    (witness : Type u) :
    CompletionCriterionAtUniverse witness ↔
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  (completionCriterionAtUniverse_iff_poincareConjectureStatement witness).trans
    poincareConjectureStatement_iff_poincare_completion_payload

/--
The project target/canonical topological statement iff is definitionally the
identity iff.
-/
theorem poincareConjectureStatement_iff_canonical_three_sphere_statement_eq :
    poincareConjectureStatement_iff_canonical_three_sphere_statement =
      Iff.rfl := by
  apply Subsingleton.elim

/--
The project smooth target/canonical smooth statement iff is definitionally the
identity iff.
-/
theorem smoothPoincareConjectureStatement_iff_canonical_smooth_three_sphere_statement_eq :
    smoothPoincareConjectureStatement_iff_canonical_smooth_three_sphere_statement =
      Iff.rfl := by
  apply Subsingleton.elim

/--
The completion criterion/project target iff is definitionally the identity iff.
-/
theorem completionCriterionAtUniverse_iff_poincareConjectureStatement_eq
    (witness : Type u) :
    completionCriterionAtUniverse_iff_poincareConjectureStatement witness =
      Iff.rfl := by
  apply Subsingleton.elim

/--
Changing the witness index for the completion criterion keeps the same proof.
-/
theorem completionCriterionAtUniverse_of_completionCriterionAtUniverse_eq
    (source target : Type u)
    (h : CompletionCriterionAtUniverse source) :
    completionCriterionAtUniverse_of_completionCriterionAtUniverse
      source target h = h := by
  apply Subsingleton.elim

/--
Any two completion criteria are equivalent by definitional identity.
-/
theorem completionCriterionAtUniverse_iff_completionCriterionAtUniverse_eq
    (source target : Type u) :
    completionCriterionAtUniverse_iff_completionCriterionAtUniverse
      source target = Iff.rfl := by
  apply Subsingleton.elim

/--
A proof of the project target discharges the completion criterion by identity.
-/
theorem completionCriterionAtUniverse_of_poincareConjectureStatement_eq
    (witness : Type u) (h : PoincareConjectureStatement.{u}) :
    completionCriterionAtUniverse_of_poincareConjectureStatement
      witness h = h := by
  apply Subsingleton.elim

/--
The project target completion payload is the target proof paired with the named
criterion projection.
-/
theorem poincare_completion_payload_of_poincareConjectureStatement_eq
    (h : PoincareConjectureStatement.{u}) :
    poincare_completion_payload_of_poincareConjectureStatement h =
      ⟨h, fun witness =>
        completionCriterionAtUniverse_of_poincareConjectureStatement
          witness h⟩ := by
  apply Subsingleton.elim

/--
The project completion payload target projection destructures the payload.
-/
theorem poincareConjectureStatement_of_poincare_completion_payload_eq
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    poincareConjectureStatement_of_poincare_completion_payload payload =
      (by
        rcases payload with ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The project completion payload criterion projection destructures the payload.
-/
theorem completionCriterionAtUniverse_of_poincare_completion_payload_eq
    (witness : Type u)
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    completionCriterionAtUniverse_of_poincare_completion_payload
      witness payload =
      (by
        rcases payload with ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The project target/completion-payload iff is the pair of named payload
constructor and target projection.
-/
theorem poincareConjectureStatement_iff_poincare_completion_payload_eq :
    poincareConjectureStatement_iff_poincare_completion_payload =
      ⟨poincare_completion_payload_of_poincareConjectureStatement,
        poincareConjectureStatement_of_poincare_completion_payload⟩ := by
  apply Subsingleton.elim

/--
A completion criterion proof gives the project target by identity.
-/
theorem poincareConjectureStatement_of_completionCriterionAtUniverse_eq
    (witness : Type u) (h : CompletionCriterionAtUniverse witness) :
    poincareConjectureStatement_of_completionCriterionAtUniverse
      witness h = h := by
  apply Subsingleton.elim

/--
The completion-criterion payload constructor factors through the named project
target projection.
-/
theorem poincare_completion_payload_of_completionCriterionAtUniverse_eq
    (witness : Type u) (h : CompletionCriterionAtUniverse witness) :
    poincare_completion_payload_of_completionCriterionAtUniverse witness h =
      poincare_completion_payload_of_poincareConjectureStatement
        (poincareConjectureStatement_of_completionCriterionAtUniverse
          witness h) := by
  apply Subsingleton.elim

/--
The completion criterion/completion-payload iff is the composition of the
criterion-to-target iff and the target-to-payload iff.
-/
theorem completionCriterionAtUniverse_iff_poincare_completion_payload_eq
    (witness : Type u) :
    completionCriterionAtUniverse_iff_poincare_completion_payload witness =
      (completionCriterionAtUniverse_iff_poincareConjectureStatement
        witness).trans poincareConjectureStatement_iff_poincare_completion_payload := by
  apply Subsingleton.elim

end Poincare
