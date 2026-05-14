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

/-- The concrete north-pole point of the target 3-sphere. -/
noncomputable def threeSphere_northPole : ThreeSphere :=
  let v : EuclideanSpace ℝ (Fin 4) := .single 0 1
  ⟨v, by simp [v]⟩

/-- The north pole is the first coordinate unit vector, viewed on the unit sphere. -/
theorem threeSphere_northPole_eq :
    threeSphere_northPole =
      (let v : EuclideanSpace ℝ (Fin 4) := .single 0 1
       ⟨v, by simp [v]⟩) :=
  rfl

/-- A concrete equatorial point of the target 3-sphere, used as a chart-overlap basepoint. -/
noncomputable def threeSphere_equatorPoint : ThreeSphere :=
  let v : EuclideanSpace ℝ (Fin 4) := .single 1 1
  ⟨v, by simp [v]⟩

/-- The equatorial point is the second coordinate unit vector, viewed on the unit sphere. -/
theorem threeSphere_equatorPoint_eq :
    threeSphere_equatorPoint =
      (let v : EuclideanSpace ℝ (Fin 4) := .single 1 1
       ⟨v, by simp [v]⟩) :=
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

/--
The ambient vector space for `ThreeSphere` has the finrank required by
mathlib's `stereographic' 3` chart constructor.
-/
instance threeSphere_stereographic_finrank_fact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp [EuclideanSpace]⟩

/--
The stereographic chart at a point of the standard `ThreeSphere` identifies
its source, the punctured sphere away from that point, with `ℝ³`.
-/
noncomputable def threeSphere_stereographic_source_homeomorph
    (v : ThreeSphere) :
    (stereographic' 3 v).source ≃ₜ EuclideanSpace ℝ (Fin 3) :=
  (stereographic' 3 v).toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (stereographic'_target v)).trans
      (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 3))))

/--
The stereographic source homeomorphism is exactly the source-target
homeomorphism of the stereographic chart followed by the target-universe
identification.
-/
theorem threeSphere_stereographic_source_homeomorph_eq
    (v : ThreeSphere) :
    threeSphere_stereographic_source_homeomorph v =
      (stereographic' 3 v).toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target v)).trans
          (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 3)))) :=
  rfl

/--
Each stereographic source of `ThreeSphere` is simply connected, because it is
homeomorphic to the contractible Euclidean space `ℝ³`.
-/
theorem threeSphere_stereographic_source_simplyConnectedSpace
    (v : ThreeSphere) :
    SimplyConnectedSpace (stereographic' 3 v).source :=
  (threeSphere_stereographic_source_homeomorph v).toHomotopyEquiv.simplyConnectedSpace

/--
The simple-connectedness witness for a stereographic source is obtained by
transporting the Euclidean-space witness across the stereographic
homeomorphism.
-/
theorem threeSphere_stereographic_source_simplyConnectedSpace_eq
    (v : ThreeSphere) :
    threeSphere_stereographic_source_simplyConnectedSpace v =
      (threeSphere_stereographic_source_homeomorph v).toHomotopyEquiv.simplyConnectedSpace := by
  apply Subsingleton.elim

/--
The source of the stereographic chart at `v` is the complement of the point
`v`.
-/
theorem threeSphere_stereographic_source_eq_compl_singleton
    (v : ThreeSphere) :
    (stereographic' 3 v).source = {v}ᶜ :=
  stereographic'_source v

/--
The source-complement statement is exactly mathlib's stereographic-source
description.
-/
theorem threeSphere_stereographic_source_eq_compl_singleton_eq
    (v : ThreeSphere) :
    threeSphere_stereographic_source_eq_compl_singleton v =
      stereographic'_source v := by
  apply Subsingleton.elim

/-- A stereographic source is an open subset of the target sphere. -/
theorem threeSphere_stereographic_source_isOpen
    (v : ThreeSphere) :
    IsOpen (stereographic' 3 v).source :=
  (stereographic' 3 v).open_source

/-- The openness witness for a stereographic source is the open-source field of the chart. -/
theorem threeSphere_stereographic_source_isOpen_eq
    (v : ThreeSphere) :
    threeSphere_stereographic_source_isOpen v =
      (stereographic' 3 v).open_source := by
  apply Subsingleton.elim

/--
The stereographic sources at antipodal points cover the whole `ThreeSphere`.
-/
theorem threeSphere_stereographic_antipodal_sources_cover
    (v : ThreeSphere) :
    (stereographic' 3 v).source ∪ (stereographic' 3 (-v)).source =
      Set.univ := by
  rw [threeSphere_stereographic_source_eq_compl_singleton,
    threeSphere_stereographic_source_eq_compl_singleton]
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  by_cases hx : x = v
  · right
    intro hxneg
    have hv : (v : EuclideanSpace ℝ (Fin 4)) = -(v : EuclideanSpace ℝ (Fin 4)) := by
      exact congrArg Subtype.val (hx.symm.trans hxneg)
    have hvzero : (v : EuclideanSpace ℝ (Fin 4)) = 0 := by
      have hsum :
          (v : EuclideanSpace ℝ (Fin 4)) + (v : EuclideanSpace ℝ (Fin 4)) =
            0 := by
        nth_rewrite 2 [hv]
        exact add_neg_cancel _
      have htwo : (2 : ℝ) • (v : EuclideanSpace ℝ (Fin 4)) = 0 := by
        simpa [two_smul] using hsum
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hvnorm : ‖(v : EuclideanSpace ℝ (Fin 4))‖ = 1 :=
      norm_eq_of_mem_sphere v
    have : (0 : ℝ) = 1 := by
      rw [← hvnorm, hvzero, norm_zero]
    norm_num at this
  · exact Or.inl hx

/--
The antipodal-source cover statement is exactly the complement-of-singleton
description of the two stereographic sources.
-/
theorem threeSphere_stereographic_antipodal_sources_cover_eq
    (v : ThreeSphere) :
    threeSphere_stereographic_antipodal_sources_cover v =
      (by
        rw [threeSphere_stereographic_source_eq_compl_singleton,
          threeSphere_stereographic_source_eq_compl_singleton]
        ext x
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
          Set.mem_univ, iff_true]
        by_cases hx : x = v
        · right
          intro hxneg
          have hv :
              (v : EuclideanSpace ℝ (Fin 4)) =
                -(v : EuclideanSpace ℝ (Fin 4)) := by
            exact congrArg Subtype.val (hx.symm.trans hxneg)
          have hvzero : (v : EuclideanSpace ℝ (Fin 4)) = 0 := by
            have hsum :
                (v : EuclideanSpace ℝ (Fin 4)) +
                    (v : EuclideanSpace ℝ (Fin 4)) =
                  0 := by
              nth_rewrite 2 [hv]
              exact add_neg_cancel _
            have htwo :
                (2 : ℝ) • (v : EuclideanSpace ℝ (Fin 4)) = 0 := by
              simpa [two_smul] using hsum
            exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
          have hvnorm : ‖(v : EuclideanSpace ℝ (Fin 4))‖ = 1 :=
            norm_eq_of_mem_sphere v
          have : (0 : ℝ) = 1 := by
            rw [← hvnorm, hvzero, norm_zero]
          norm_num at this
        · exact Or.inl hx) := by
  apply Subsingleton.elim

/--
The overlap of two antipodal stereographic sources is the complement of the two
excluded antipodal points.
-/
theorem threeSphere_stereographic_antipodal_sources_inter
    (v : ThreeSphere) :
    (stereographic' 3 v).source ∩ (stereographic' 3 (-v)).source =
      ({v} ∪ {-v})ᶜ := by
  rw [threeSphere_stereographic_source_eq_compl_singleton,
    threeSphere_stereographic_source_eq_compl_singleton]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_union, not_or]

/--
The antipodal-source overlap statement is exactly the complement-of-two-points
description obtained from the two stereographic source descriptions.
-/
theorem threeSphere_stereographic_antipodal_sources_inter_eq
    (v : ThreeSphere) :
    threeSphere_stereographic_antipodal_sources_inter v =
      (by
        rw [threeSphere_stereographic_source_eq_compl_singleton,
          threeSphere_stereographic_source_eq_compl_singleton]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
          Set.mem_union, not_or]) := by
  apply Subsingleton.elim

/-- The overlap of two antipodal stereographic sources is open. -/
theorem threeSphere_stereographic_antipodal_sources_inter_isOpen
    (v : ThreeSphere) :
    IsOpen ((stereographic' 3 v).source ∩ (stereographic' 3 (-v)).source) :=
  (threeSphere_stereographic_source_isOpen v).inter
    (threeSphere_stereographic_source_isOpen (-v))

/--
The openness witness for the antipodal-source overlap is the intersection of
the two stereographic open-source witnesses.
-/
theorem threeSphere_stereographic_antipodal_sources_inter_isOpen_eq
    (v : ThreeSphere) :
    threeSphere_stereographic_antipodal_sources_inter_isOpen v =
      (threeSphere_stereographic_source_isOpen v).inter
        (threeSphere_stereographic_source_isOpen (-v)) := by
  apply Subsingleton.elim

/--
The explicit equatorial point lies in the overlap of the north- and south-pole
stereographic sources.
-/
theorem threeSphere_equatorPoint_mem_northPole_antipodal_sources_inter :
    threeSphere_equatorPoint ∈
      (stereographic' 3 threeSphere_northPole).source ∩
        (stereographic' 3 (-threeSphere_northPole)).source := by
  rw [threeSphere_stereographic_antipodal_sources_inter]
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, not_or]
  constructor
  · intro h
    have hcoord := congrArg
      (fun w : EuclideanSpace ℝ (Fin 4) => w 0)
      (congrArg Subtype.val h)
    norm_num [threeSphere_equatorPoint, threeSphere_northPole] at hcoord
  · intro h
    have hcoord := congrArg
      (fun w : EuclideanSpace ℝ (Fin 4) => w 0)
      (congrArg Subtype.val h)
    norm_num [threeSphere_equatorPoint, threeSphere_northPole] at hcoord

/--
The explicit overlap-basepoint membership proof is exactly the two coordinate
separations from the north and south poles after the overlap is rewritten as the
complement of those two points.
-/
theorem threeSphere_equatorPoint_mem_northPole_antipodal_sources_inter_eq :
    threeSphere_equatorPoint_mem_northPole_antipodal_sources_inter =
      (by
        rw [threeSphere_stereographic_antipodal_sources_inter]
        simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, not_or]
        constructor
        · intro h
          have hcoord := congrArg
            (fun w : EuclideanSpace ℝ (Fin 4) => w 0)
            (congrArg Subtype.val h)
          norm_num [threeSphere_equatorPoint, threeSphere_northPole] at hcoord
        · intro h
          have hcoord := congrArg
            (fun w : EuclideanSpace ℝ (Fin 4) => w 0)
            (congrArg Subtype.val h)
          norm_num [threeSphere_equatorPoint, threeSphere_northPole] at hcoord) := by
  apply Subsingleton.elim

/-- The south pole lies in the north-pole stereographic source. -/
theorem threeSphere_southPole_mem_northPole_stereographic_source :
    (-threeSphere_northPole) ∈ (stereographic' 3 threeSphere_northPole).source := by
  rw [threeSphere_stereographic_source_eq_compl_singleton]
  intro h
  have hcoord := congrArg
    (fun w : EuclideanSpace ℝ (Fin 4) => w 0)
    (congrArg Subtype.val h)
  norm_num [threeSphere_northPole] at hcoord

/--
The south-pole source-membership proof is the coordinate separation of the
south pole from the north pole after rewriting the stereographic source as a
singleton complement.
-/
theorem threeSphere_southPole_mem_northPole_stereographic_source_eq :
    threeSphere_southPole_mem_northPole_stereographic_source =
      (by
        rw [threeSphere_stereographic_source_eq_compl_singleton]
        intro h
        have hcoord := congrArg
          (fun w : EuclideanSpace ℝ (Fin 4) => w 0)
          (congrArg Subtype.val h)
        norm_num [threeSphere_northPole] at hcoord) := by
  apply Subsingleton.elim

/-- The south pole as a point of the north-pole stereographic source. -/
noncomputable def threeSphere_southPoleInNorthSource :
    (stereographic' 3 threeSphere_northPole).source :=
  ⟨-threeSphere_northPole, threeSphere_southPole_mem_northPole_stereographic_source⟩

/-- The south-pole source point is the south pole with the named source-membership proof. -/
theorem threeSphere_southPoleInNorthSource_eq :
    threeSphere_southPoleInNorthSource =
      ⟨-threeSphere_northPole,
        threeSphere_southPole_mem_northPole_stereographic_source⟩ :=
  rfl

/--
The image of the south pole in the north-pole stereographic chart.  Its
complement in `ℝ³` is the target-side model for the north/south chart overlap.
-/
noncomputable def threeSphere_southPole_northChartImage :
    EuclideanSpace ℝ (Fin 3) :=
  threeSphere_stereographic_source_homeomorph threeSphere_northPole
    threeSphere_southPoleInNorthSource

/--
The south-pole north-chart image is obtained by applying the named source
homeomorphism to the south pole as a point of the north-pole source.
-/
theorem threeSphere_southPole_northChartImage_eq :
    threeSphere_southPole_northChartImage =
      threeSphere_stereographic_source_homeomorph threeSphere_northPole
        threeSphere_southPoleInNorthSource :=
  rfl

/--
The verified north/south stereographic open-cover data for the standard
3-sphere.  This packages the concrete inputs needed by a later Van Kampen or
loop-fragment argument without asserting that missing argument.
-/
structure ThreeSphereStereographicOpenCoverPackage where
  northSourceSimplyConnected :
    SimplyConnectedSpace (stereographic' 3 threeSphere_northPole).source
  southSourceSimplyConnected :
    SimplyConnectedSpace (stereographic' 3 (-threeSphere_northPole)).source
  northSourceOpen : IsOpen (stereographic' 3 threeSphere_northPole).source
  southSourceOpen : IsOpen (stereographic' 3 (-threeSphere_northPole)).source
  cover :
    (stereographic' 3 threeSphere_northPole).source ∪
        (stereographic' 3 (-threeSphere_northPole)).source =
      Set.univ
  overlapOpen :
    IsOpen ((stereographic' 3 threeSphere_northPole).source ∩
      (stereographic' 3 (-threeSphere_northPole)).source)
  overlapBasepoint :
    threeSphere_equatorPoint ∈
      (stereographic' 3 threeSphere_northPole).source ∩
        (stereographic' 3 (-threeSphere_northPole)).source

/-- The concrete north/south stereographic open-cover package for `ThreeSphere`. -/
noncomputable def threeSphere_stereographicOpenCoverPackage :
    ThreeSphereStereographicOpenCoverPackage where
  northSourceSimplyConnected :=
    threeSphere_stereographic_source_simplyConnectedSpace threeSphere_northPole
  southSourceSimplyConnected :=
    threeSphere_stereographic_source_simplyConnectedSpace (-threeSphere_northPole)
  northSourceOpen :=
    threeSphere_stereographic_source_isOpen threeSphere_northPole
  southSourceOpen :=
    threeSphere_stereographic_source_isOpen (-threeSphere_northPole)
  cover :=
    threeSphere_stereographic_antipodal_sources_cover threeSphere_northPole
  overlapOpen :=
    threeSphere_stereographic_antipodal_sources_inter_isOpen threeSphere_northPole
  overlapBasepoint :=
    threeSphere_equatorPoint_mem_northPole_antipodal_sources_inter

/--
The stereographic open-cover package is assembled exactly from the named
north/south chart-domain, cover, overlap, and basepoint witnesses.
-/
theorem threeSphere_stereographicOpenCoverPackage_eq :
    threeSphere_stereographicOpenCoverPackage =
      { northSourceSimplyConnected :=
          threeSphere_stereographic_source_simplyConnectedSpace threeSphere_northPole
        southSourceSimplyConnected :=
          threeSphere_stereographic_source_simplyConnectedSpace (-threeSphere_northPole)
        northSourceOpen :=
          threeSphere_stereographic_source_isOpen threeSphere_northPole
        southSourceOpen :=
          threeSphere_stereographic_source_isOpen (-threeSphere_northPole)
        cover :=
          threeSphere_stereographic_antipodal_sources_cover threeSphere_northPole
        overlapOpen :=
          threeSphere_stereographic_antipodal_sources_inter_isOpen threeSphere_northPole
        overlapBasepoint :=
          threeSphere_equatorPoint_mem_northPole_antipodal_sources_inter } := by
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

/--
The stereographic target space `ℝ³` has rank greater than one, the input needed
for path-connectedness of complements of singletons.
-/
theorem euclideanThree_rank_gt_one :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  rw [(EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.rank_eq]
  rw [rank_fin_fun]
  norm_num

/-- The `ℝ³` rank witness is the finite-dimensional rank computation. -/
theorem euclideanThree_rank_gt_one_eq :
    euclideanThree_rank_gt_one =
      (by
        rw [(EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.rank_eq]
        rw [rank_fin_fun]
        norm_num) := by
  apply Subsingleton.elim

/-- In the stereographic target `ℝ³`, the complement of any point is path-connected. -/
theorem euclideanThree_isPathConnected_compl_singleton
    (x : EuclideanSpace ℝ (Fin 3)) :
    IsPathConnected ({x}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
  isPathConnected_compl_singleton_of_one_lt_rank euclideanThree_rank_gt_one x

/--
The punctured-`ℝ³` path-connectedness witness is mathlib's complement-of-a-point
result applied to the stereographic target rank computation.
-/
theorem euclideanThree_isPathConnected_compl_singleton_eq
    (x : EuclideanSpace ℝ (Fin 3)) :
    euclideanThree_isPathConnected_compl_singleton x =
      isPathConnected_compl_singleton_of_one_lt_rank euclideanThree_rank_gt_one x := by
  apply Subsingleton.elim

/-- The subtype of punctured `ℝ³` is path-connected. -/
theorem euclideanThree_compl_singleton_pathConnectedSpace
    (x : EuclideanSpace ℝ (Fin 3)) :
    PathConnectedSpace ({x}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (euclideanThree_isPathConnected_compl_singleton x)

/--
The punctured-`ℝ³` subtype path-connectedness is induced from the corresponding
set-level path-connectedness witness.
-/
theorem euclideanThree_compl_singleton_pathConnectedSpace_eq
    (x : EuclideanSpace ℝ (Fin 3)) :
    euclideanThree_compl_singleton_pathConnectedSpace x =
      isPathConnected_iff_pathConnectedSpace.mp
        (euclideanThree_isPathConnected_compl_singleton x) := by
  apply Subsingleton.elim

/--
The complement of the south-pole image in the north-pole stereographic chart is
path-connected in `ℝ³`.
-/
theorem threeSphere_northChartImage_compl_southPole_isPathConnected :
    IsPathConnected
      ({threeSphere_southPole_northChartImage}ᶜ :
        Set (EuclideanSpace ℝ (Fin 3))) :=
  euclideanThree_isPathConnected_compl_singleton
    threeSphere_southPole_northChartImage

/--
The chart-side overlap path-connectedness input is the punctured-`ℝ³`
path-connectedness theorem applied to the south-pole chart image.
-/
theorem threeSphere_northChartImage_compl_southPole_isPathConnected_eq :
    threeSphere_northChartImage_compl_southPole_isPathConnected =
      euclideanThree_isPathConnected_compl_singleton
        threeSphere_southPole_northChartImage := by
  apply Subsingleton.elim

/--
The subtype complement of the south-pole image in the north-pole stereographic
chart is path-connected.
-/
theorem threeSphere_northChartImage_compl_southPole_pathConnectedSpace :
    PathConnectedSpace
      ({threeSphere_southPole_northChartImage}ᶜ :
        Set (EuclideanSpace ℝ (Fin 3))) :=
  euclideanThree_compl_singleton_pathConnectedSpace
    threeSphere_southPole_northChartImage

/--
The chart-side overlap subtype path-connectedness is the punctured-`ℝ³` subtype
path-connectedness theorem applied to the south-pole chart image.
-/
theorem threeSphere_northChartImage_compl_southPole_pathConnectedSpace_eq :
    threeSphere_northChartImage_compl_southPole_pathConnectedSpace =
      euclideanThree_compl_singleton_pathConnectedSpace
        threeSphere_southPole_northChartImage := by
  apply Subsingleton.elim

/--
Inside the north-pole stereographic source, the north/south overlap is exactly
the complement of the south-pole source point.
-/
theorem threeSphere_northSource_southSource_preimage_eq_compl_southPole :
    {p : (stereographic' 3 threeSphere_northPole).source |
        (p : ThreeSphere) ∈ (stereographic' 3 (-threeSphere_northPole)).source} =
      {threeSphere_southPoleInNorthSource}ᶜ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  have hmem :
      ((p : ThreeSphere) ∈ (stereographic' 3 (-threeSphere_northPole)).source) ↔
        (p : ThreeSphere) ≠ -threeSphere_northPole := by
    rw [threeSphere_stereographic_source_eq_compl_singleton]
    simp
  rw [hmem]
  constructor
  · intro hp hsub
    exact hp (congrArg Subtype.val hsub)
  · intro hp hval
    exact hp (Subtype.ext hval)

/--
The north-source description of the north/south overlap is obtained by rewriting
the south-pole stereographic source as the complement of the south pole.
-/
theorem threeSphere_northSource_southSource_preimage_eq_compl_southPole_eq :
    threeSphere_northSource_southSource_preimage_eq_compl_southPole =
      (by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
        have hmem :
            ((p : ThreeSphere) ∈ (stereographic' 3 (-threeSphere_northPole)).source) ↔
              (p : ThreeSphere) ≠ -threeSphere_northPole := by
          rw [threeSphere_stereographic_source_eq_compl_singleton]
          simp
        rw [hmem]
        constructor
        · intro hp hsub
          exact hp (congrArg Subtype.val hsub)
        · intro hp hval
          exact hp (Subtype.ext hval)) := by
  apply Subsingleton.elim

/--
The north-pole stereographic homeomorphism restricts to a homeomorphism from
the north-source overlap model to punctured `ℝ³`, with the puncture at the
south-pole chart image.
-/
noncomputable def threeSphere_northSourceOverlap_homeomorph_puncturedChart :
    ({threeSphere_southPoleInNorthSource}ᶜ :
      Set (stereographic' 3 threeSphere_northPole).source) ≃ₜ
      ({threeSphere_southPole_northChartImage}ᶜ :
        Set (EuclideanSpace ℝ (Fin 3))) :=
  (threeSphere_stereographic_source_homeomorph threeSphere_northPole).subtype
    (fun p => by
      simp [threeSphere_southPole_northChartImage])

/--
The restricted overlap homeomorphism is the subtype restriction of the named
north-pole stereographic source homeomorphism to the complement of the
south-pole source point.
-/
theorem threeSphere_northSourceOverlap_homeomorph_puncturedChart_eq :
    threeSphere_northSourceOverlap_homeomorph_puncturedChart =
      (threeSphere_stereographic_source_homeomorph threeSphere_northPole).subtype
        (fun p => by
          simp [threeSphere_southPole_northChartImage]) :=
  rfl

/--
The north-source model of the north/south overlap is path-connected, transported
from punctured `ℝ³` across the restricted stereographic homeomorphism.
-/
theorem threeSphere_northSourceOverlap_pathConnectedSpace :
    PathConnectedSpace
      ({threeSphere_southPoleInNorthSource}ᶜ :
        Set (stereographic' 3 threeSphere_northPole).source) := by
  letI : PathConnectedSpace
      ({threeSphere_southPole_northChartImage}ᶜ :
        Set (EuclideanSpace ℝ (Fin 3))) :=
    threeSphere_northChartImage_compl_southPole_pathConnectedSpace
  exact
    threeSphere_northSourceOverlap_homeomorph_puncturedChart.symm.surjective.pathConnectedSpace
      threeSphere_northSourceOverlap_homeomorph_puncturedChart.symm.continuous

/--
The north-source overlap path-connectedness witness is transported from the
punctured-chart path-connectedness witness by the inverse restricted
homeomorphism.
-/
theorem threeSphere_northSourceOverlap_pathConnectedSpace_eq :
    threeSphere_northSourceOverlap_pathConnectedSpace =
      (by
        letI : PathConnectedSpace
            ({threeSphere_southPole_northChartImage}ᶜ :
              Set (EuclideanSpace ℝ (Fin 3))) :=
          threeSphere_northChartImage_compl_southPole_pathConnectedSpace
        exact
          threeSphere_northSourceOverlap_homeomorph_puncturedChart.symm.surjective.pathConnectedSpace
            threeSphere_northSourceOverlap_homeomorph_puncturedChart.symm.continuous) := by
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
    Nonempty ThreeSphere :=
  ⟨threeSphere_northPole⟩

/-- The target 3-sphere nonemptiness witness is the named north-pole point. -/
theorem threeSphere_nonempty_eq :
    threeSphere_nonempty =
      ⟨threeSphere_northPole⟩ := by
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
Direct-simple standard-sphere target prerequisites, explicitly named to match
the corresponding one-point compactification payload route.
-/
theorem threeSphere_target_prerequisites_of_simpleConnectedSpace
    [SimplyConnectedSpace ThreeSphere] :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere :=
  threeSphere_target_prerequisites

/-- The direct-simple target prerequisite payload is the named full target payload. -/
theorem threeSphere_target_prerequisites_of_simpleConnectedSpace_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_target_prerequisites_of_simpleConnectedSpace =
      threeSphere_target_prerequisites := by
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

/--
Direct-simple standard-sphere homotopy prerequisites, explicitly named to match
the corresponding one-point compactification payload route.
-/
theorem threeSphere_homotopy_prerequisites_of_simpleConnectedSpace
    [SimplyConnectedSpace ThreeSphere] :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _locPath : LocPathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere :=
  threeSphere_homotopy_prerequisites

/-- The direct-simple homotopy prerequisite payload is the named full homotopy payload. -/
theorem threeSphere_homotopy_prerequisites_of_simpleConnectedSpace_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_homotopy_prerequisites_of_simpleConnectedSpace =
      threeSphere_homotopy_prerequisites := by
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

/--
The north-pole based loop-nullhomotopy obligation for the standard 3-sphere.
This is the concrete basepoint-specialized form of the remaining
simple-connectedness input for `ThreeSphere`.
-/
def ThreeSphereNorthPoleLoopNullhomotopyStatement : Prop :=
  ThreeSphereBasedLoopNullhomotopyStatement threeSphere_northPole

/--
The north-pole loop-nullhomotopy obligation expands to nullhomotopy of every
loop based at the explicit north-pole point.
-/
theorem threeSphereNorthPoleLoopNullhomotopyStatement_eq :
    ThreeSphereNorthPoleLoopNullhomotopyStatement =
      (∀ γ : Path threeSphere_northPole threeSphere_northPole,
        Path.Homotopic γ (Path.refl threeSphere_northPole)) :=
  rfl

/--
For the standard sphere, simple-connectedness is equivalent to nullhomotopy of
all loops based at the explicit north-pole point, because path-connectedness has
already been proved.
-/
theorem threeSphere_simplyConnectedSpace_iff_northPoleLoopNullhomotopyStatement :
    SimplyConnectedSpace ThreeSphere ↔
      ThreeSphereNorthPoleLoopNullhomotopyStatement :=
  threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement
    threeSphere_northPole

/--
The north-pole simple-connectedness reduction is the existing based-loop
criterion specialized to the named north-pole point.
-/
theorem threeSphere_simplyConnectedSpace_iff_northPoleLoopNullhomotopyStatement_eq :
    threeSphere_simplyConnectedSpace_iff_northPoleLoopNullhomotopyStatement =
      threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement
        threeSphere_northPole :=
  rfl

/--
A north-pole based loop-nullhomotopy proof supplies simple-connectedness of
`S^3`.
-/
theorem threeSphere_simplyConnectedSpace_of_northPoleLoopNullhomotopyStatement
    (h : ThreeSphereNorthPoleLoopNullhomotopyStatement) :
    SimplyConnectedSpace ThreeSphere :=
  threeSphere_simplyConnectedSpace_iff_northPoleLoopNullhomotopyStatement.mpr h

/--
The north-pole loop-nullhomotopy-to-simple-connectedness route is the reverse
projection of the named north-pole criterion.
-/
theorem threeSphere_simplyConnectedSpace_of_northPoleLoopNullhomotopyStatement_eq :
    threeSphere_simplyConnectedSpace_of_northPoleLoopNullhomotopyStatement =
      threeSphere_simplyConnectedSpace_iff_northPoleLoopNullhomotopyStatement.mpr := by
  funext h
  apply Subsingleton.elim

/--
A supplied simple-connectedness instance gives north-pole based
loop-nullhomotopy.
-/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace ThreeSphere] :
    ThreeSphereNorthPoleLoopNullhomotopyStatement :=
  threeSphere_simplyConnectedSpace_iff_northPoleLoopNullhomotopyStatement.mp
    inferInstance

/--
The simple-connectedness-to-north-pole-loop route is the forward projection of
the named north-pole criterion.
-/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_northPoleLoopNullhomotopyStatement_of_simplyConnectedSpace =
      threeSphere_simplyConnectedSpace_iff_northPoleLoopNullhomotopyStatement.mp
        inferInstance := by
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

/--
The remaining Van Kampen-style obligation for the north/south stereographic
open cover: every loop based at the explicit equatorial overlap point is
null-homotopic.
-/
def ThreeSphereStereographicVanKampenLoopStatement : Prop :=
  ThreeSphereBasedLoopNullhomotopyStatement threeSphere_equatorPoint

/--
The stereographic Van Kampen loop obligation is exactly based loop
nullhomotopy at the explicit overlap basepoint.
-/
theorem threeSphereStereographicVanKampenLoopStatement_eq :
    ThreeSphereStereographicVanKampenLoopStatement =
      ThreeSphereBasedLoopNullhomotopyStatement threeSphere_equatorPoint :=
  rfl

/--
For the standard sphere, simple-connectedness is equivalent to the
stereographic Van Kampen loop obligation at the explicit equatorial overlap
basepoint.
-/
theorem threeSphere_simplyConnectedSpace_iff_stereographicVanKampenLoopStatement :
    SimplyConnectedSpace ThreeSphere ↔
      ThreeSphereStereographicVanKampenLoopStatement := by
  rw [threeSphereStereographicVanKampenLoopStatement_eq]
  exact threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement
    threeSphere_equatorPoint

/--
The stereographic Van Kampen equivalence is exactly the based-loop
simple-connectedness criterion at the equatorial overlap basepoint.
-/
theorem threeSphere_simplyConnectedSpace_iff_stereographicVanKampenLoopStatement_eq :
    threeSphere_simplyConnectedSpace_iff_stereographicVanKampenLoopStatement =
      (by
        rw [threeSphereStereographicVanKampenLoopStatement_eq]
        exact threeSphere_simplyConnectedSpace_iff_basedLoopNullhomotopyStatement
          threeSphere_equatorPoint) := by
  apply Subsingleton.elim

/--
A proof of the stereographic Van Kampen loop obligation supplies
simple-connectedness of the standard 3-sphere through the existing
change-of-basepoint criterion.
-/
theorem threeSphere_simplyConnectedSpace_of_stereographicVanKampenLoopStatement
    (h : ThreeSphereStereographicVanKampenLoopStatement) :
    SimplyConnectedSpace ThreeSphere :=
  threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h

/--
The stereographic Van Kampen loop route to simple-connectedness is exactly the
based-loop route at the explicit equatorial overlap basepoint.
-/
theorem threeSphere_simplyConnectedSpace_of_stereographicVanKampenLoopStatement_eq :
    threeSphere_simplyConnectedSpace_of_stereographicVanKampenLoopStatement =
      (fun h : ThreeSphereStereographicVanKampenLoopStatement =>
        threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement
          (basepoint := threeSphere_equatorPoint) h) := by
  funext h
  apply Subsingleton.elim

/--
A supplied simple-connectedness instance gives the stereographic Van Kampen
loop obligation at the explicit equatorial overlap basepoint.
-/
theorem threeSphere_stereographicVanKampenLoopStatement_of_simplyConnectedSpace
    [SimplyConnectedSpace ThreeSphere] :
    ThreeSphereStereographicVanKampenLoopStatement :=
  threeSphere_simplyConnectedSpace_iff_stereographicVanKampenLoopStatement.mp
    inferInstance

/--
The simple-connectedness-to-stereographic-loop route is the forward projection
of the named stereographic Van Kampen equivalence.
-/
theorem threeSphere_stereographicVanKampenLoopStatement_of_simplyConnectedSpace_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_stereographicVanKampenLoopStatement_of_simplyConnectedSpace =
      threeSphere_simplyConnectedSpace_iff_stereographicVanKampenLoopStatement.mp
        inferInstance := by
  apply Subsingleton.elim

/--
A stereographic Van Kampen loop proof supplies the full target-prerequisite
tuple for the standard 3-sphere.
-/
theorem threeSphere_target_prerequisites_of_stereographicVanKampenLoopStatement
    (h : ThreeSphereStereographicVanKampenLoopStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_stereographicVanKampenLoopStatement h
  exact threeSphere_target_prerequisites_of_simpleConnectedSpace

/--
The stereographic Van Kampen target-prerequisite route is simple-connectedness
from the equatorial based-loop obligation followed by the direct-simple
target-prerequisite payload.
-/
theorem threeSphere_target_prerequisites_of_stereographicVanKampenLoopStatement_eq :
    threeSphere_target_prerequisites_of_stereographicVanKampenLoopStatement =
      (fun h : ThreeSphereStereographicVanKampenLoopStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_stereographicVanKampenLoopStatement h
        threeSphere_target_prerequisites_of_simpleConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/--
A stereographic Van Kampen loop proof supplies the full homotopy-prerequisite
tuple for the standard 3-sphere.
-/
theorem threeSphere_homotopy_prerequisites_of_stereographicVanKampenLoopStatement
    (h : ThreeSphereStereographicVanKampenLoopStatement) :
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
    threeSphere_simplyConnectedSpace_of_stereographicVanKampenLoopStatement h
  exact threeSphere_homotopy_prerequisites_of_simpleConnectedSpace

/--
The stereographic Van Kampen homotopy-prerequisite route is
simple-connectedness from the equatorial based-loop obligation followed by the
direct-simple homotopy-prerequisite payload.
-/
theorem threeSphere_homotopy_prerequisites_of_stereographicVanKampenLoopStatement_eq :
    threeSphere_homotopy_prerequisites_of_stereographicVanKampenLoopStatement =
      (fun h : ThreeSphereStereographicVanKampenLoopStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_stereographicVanKampenLoopStatement h
        threeSphere_homotopy_prerequisites_of_simpleConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/--
The target-prerequisite payload for the standard sphere is equivalent to the
stereographic Van Kampen loop obligation: all other target-prerequisite
components are already named, and the payload's simple-connectedness component
recovers the stereographic loop obligation.
-/
theorem threeSphere_target_prerequisites_iff_stereographicVanKampenLoopStatement :
    (∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere) ↔
      ThreeSphereStereographicVanKampenLoopStatement := by
  constructor
  · intro h
    rcases h with
      ⟨_t2, _charted, simplyConnected, _compact, _smooth, _path,
        _connected, _nonempty⟩
    letI : SimplyConnectedSpace ThreeSphere := simplyConnected
    exact threeSphere_stereographicVanKampenLoopStatement_of_simplyConnectedSpace
  · exact threeSphere_target_prerequisites_of_stereographicVanKampenLoopStatement

/--
The target-prerequisite/stereographic-loop equivalence is obtained by projecting
simple-connectedness out of the payload in one direction and using the named
stereographic target-prerequisite route in the other.
-/
theorem threeSphere_target_prerequisites_iff_stereographicVanKampenLoopStatement_eq :
    threeSphere_target_prerequisites_iff_stereographicVanKampenLoopStatement =
      (by
        constructor
        · intro h
          rcases h with
            ⟨_t2, _charted, simplyConnected, _compact, _smooth, _path,
              _connected, _nonempty⟩
          letI : SimplyConnectedSpace ThreeSphere := simplyConnected
          exact threeSphere_stereographicVanKampenLoopStatement_of_simplyConnectedSpace
        · exact threeSphere_target_prerequisites_of_stereographicVanKampenLoopStatement) := by
  apply Subsingleton.elim

/--
The homotopy-prerequisite payload for the standard sphere is equivalent to the
stereographic Van Kampen loop obligation.
-/
theorem threeSphere_homotopy_prerequisites_iff_stereographicVanKampenLoopStatement :
    (∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _locPath : LocPathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere) ↔
      ThreeSphereStereographicVanKampenLoopStatement := by
  constructor
  · intro h
    rcases h with
      ⟨_t2, _charted, simplyConnected, _compact, _smooth, _path, _locPath,
        _connected, _nonempty⟩
    letI : SimplyConnectedSpace ThreeSphere := simplyConnected
    exact threeSphere_stereographicVanKampenLoopStatement_of_simplyConnectedSpace
  · exact threeSphere_homotopy_prerequisites_of_stereographicVanKampenLoopStatement

/--
The homotopy-prerequisite/stereographic-loop equivalence is obtained by
projecting simple-connectedness out of the payload in one direction and using
the named stereographic homotopy-prerequisite route in the other.
-/
theorem threeSphere_homotopy_prerequisites_iff_stereographicVanKampenLoopStatement_eq :
    threeSphere_homotopy_prerequisites_iff_stereographicVanKampenLoopStatement =
      (by
        constructor
        · intro h
          rcases h with
            ⟨_t2, _charted, simplyConnected, _compact, _smooth, _path, _locPath,
              _connected, _nonempty⟩
          letI : SimplyConnectedSpace ThreeSphere := simplyConnected
          exact threeSphere_stereographicVanKampenLoopStatement_of_simplyConnectedSpace
        · exact threeSphere_homotopy_prerequisites_of_stereographicVanKampenLoopStatement) := by
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
North-pole based loop-nullhomotopy supplies the full loop-nullhomotopy
obligation for `S^3`.
-/
theorem threeSphere_loopNullhomotopyStatement_of_northPoleLoopNullhomotopyStatement
    (h : ThreeSphereNorthPoleLoopNullhomotopyStatement) :
    ThreeSphereLoopNullhomotopyStatement :=
  threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h

/--
The north-pole-to-full-loop route is the generic based-loop route specialized
to the named north-pole point.
-/
theorem threeSphere_loopNullhomotopyStatement_of_northPoleLoopNullhomotopyStatement_eq :
    threeSphere_loopNullhomotopyStatement_of_northPoleLoopNullhomotopyStatement =
      (fun h : ThreeSphereNorthPoleLoopNullhomotopyStatement =>
        threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h) := by
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

/-- The `π₁` formulation supplies the fundamental-group formulation. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement
    (h : ThreeSpherePiOneSubsingletonStatement) :
    ThreeSphereFundamentalGroupSubsingletonStatement :=
  threeSphere_piOneSubsingletonStatement_iff_fundamentalGroupSubsingletonStatement.mp h

/-- The `π₁`-to-fundamental-group route is the forward equivalence projection. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement_eq :
    threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement =
      threeSphere_piOneSubsingletonStatement_iff_fundamentalGroupSubsingletonStatement.mp := by
  funext h
  apply Subsingleton.elim

/-- The fundamental-group formulation supplies the `π₁` formulation. -/
theorem threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
    (h : ThreeSphereFundamentalGroupSubsingletonStatement) :
    ThreeSpherePiOneSubsingletonStatement :=
  threeSphere_piOneSubsingletonStatement_iff_fundamentalGroupSubsingletonStatement.mpr h

/-- The fundamental-group-to-`π₁` route is the reverse equivalence projection. -/
theorem threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement =
      threeSphere_piOneSubsingletonStatement_iff_fundamentalGroupSubsingletonStatement.mpr := by
  funext h
  apply Subsingleton.elim

/-- The `π₁` formulation supplies loop-nullhomotopy through fundamental groups. -/
theorem threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement
    (h : ThreeSpherePiOneSubsingletonStatement) :
    ThreeSphereLoopNullhomotopyStatement :=
  threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
    (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement h)

/-- The `π₁`-to-loop route factors through the named fundamental-group projection. -/
theorem threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement_eq :
    threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/-- Loop-nullhomotopy supplies the `π₁` formulation through fundamental groups. -/
theorem threeSphere_piOneSubsingletonStatement_of_loopNullhomotopyStatement
    (h : ThreeSphereLoopNullhomotopyStatement) :
    ThreeSpherePiOneSubsingletonStatement :=
  threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
    (threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement h)

/-- The loop-to-`π₁` route factors through the named fundamental-group projection. -/
theorem threeSphere_piOneSubsingletonStatement_of_loopNullhomotopyStatement_eq :
    threeSphere_piOneSubsingletonStatement_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/-- Path-homotopy uniqueness supplies fundamental-group triviality through loops. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_pathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    ThreeSphereFundamentalGroupSubsingletonStatement :=
  threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement
    (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement h)

/-- The path-to-fundamental-group route factors through loop-nullhomotopy. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_pathHomotopyStatement_eq :
    threeSphere_fundamentalGroupSubsingletonStatement_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/-- Path-quotient uniqueness supplies fundamental-group triviality through paths. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_pathQuotientSubsingletonStatement
    (h : ThreeSpherePathQuotientSubsingletonStatement) :
    ThreeSphereFundamentalGroupSubsingletonStatement :=
  threeSphere_fundamentalGroupSubsingletonStatement_of_pathHomotopyStatement
    (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h)

/-- The quotient-to-fundamental-group route factors through path-homotopy. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_pathQuotientSubsingletonStatement_eq :
    threeSphere_fundamentalGroupSubsingletonStatement_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        threeSphere_fundamentalGroupSubsingletonStatement_of_pathHomotopyStatement
          (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/-- Path-homotopy uniqueness supplies the `π₁` formulation through fundamental groups. -/
theorem threeSphere_piOneSubsingletonStatement_of_pathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    ThreeSpherePiOneSubsingletonStatement :=
  threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
    (threeSphere_fundamentalGroupSubsingletonStatement_of_pathHomotopyStatement h)

/-- The path-to-`π₁` route factors through fundamental groups. -/
theorem threeSphere_piOneSubsingletonStatement_of_pathHomotopyStatement_eq :
    threeSphere_piOneSubsingletonStatement_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_pathHomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/-- Path-quotient uniqueness supplies the `π₁` formulation through fundamental groups. -/
theorem threeSphere_piOneSubsingletonStatement_of_pathQuotientSubsingletonStatement
    (h : ThreeSpherePathQuotientSubsingletonStatement) :
    ThreeSpherePiOneSubsingletonStatement :=
  threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
    (threeSphere_fundamentalGroupSubsingletonStatement_of_pathQuotientSubsingletonStatement h)

/-- The quotient-to-`π₁` route factors through fundamental groups. -/
theorem threeSphere_piOneSubsingletonStatement_of_pathQuotientSubsingletonStatement_eq :
    threeSphere_piOneSubsingletonStatement_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_pathQuotientSubsingletonStatement h)) := by
  funext h
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

/-- A based loop-nullhomotopy proof supplies path-homotopy uniqueness on `S^3`. -/
theorem threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (h : ThreeSphereBasedLoopNullhomotopyStatement basepoint) :
    ThreeSpherePathHomotopyStatement :=
  threeSphere_pathHomotopyStatement_of_loopNullhomotopyStatement
    (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h)

/-- The based-loop-to-path route factors through full loop-nullhomotopy. -/
theorem threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement h :
        ThreeSpherePathHomotopyStatement)) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        (threeSphere_pathHomotopyStatement_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h) :
            ThreeSpherePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- A based loop-nullhomotopy proof supplies path-quotient uniqueness on `S^3`. -/
theorem threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (h : ThreeSphereBasedLoopNullhomotopyStatement basepoint) :
    ThreeSpherePathQuotientSubsingletonStatement :=
  threeSphere_pathQuotientSubsingletonStatement_of_pathHomotopyStatement
    (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement h)

/-- The based-loop-to-path-quotient route factors through path-homotopy uniqueness. -/
theorem threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement h :
        ThreeSpherePathQuotientSubsingletonStatement)) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        (threeSphere_pathQuotientSubsingletonStatement_of_pathHomotopyStatement
          (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement h) :
            ThreeSpherePathQuotientSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/-- A based loop-nullhomotopy proof supplies fundamental-group triviality on `S^3`. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (h : ThreeSphereBasedLoopNullhomotopyStatement basepoint) :
    ThreeSphereFundamentalGroupSubsingletonStatement :=
  threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement
    (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h)

/-- The based-loop-to-fundamental-group route factors through full loop-nullhomotopy. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement h :
        ThreeSphereFundamentalGroupSubsingletonStatement)) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        (threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h) :
            ThreeSphereFundamentalGroupSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/-- A based loop-nullhomotopy proof supplies the `π₁` formulation on `S^3`. -/
theorem threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (h : ThreeSphereBasedLoopNullhomotopyStatement basepoint) :
    ThreeSpherePiOneSubsingletonStatement :=
  threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
    (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement h)

/-- The based-loop-to-`π₁` route factors through fundamental groups. -/
theorem threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement h :
        ThreeSpherePiOneSubsingletonStatement)) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        (threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement h) :
            ThreeSpherePiOneSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/-- A stereographic Van Kampen loop proof supplies full loop-nullhomotopy on `S^3`. -/
theorem threeSphere_loopNullhomotopyStatement_of_stereographicVanKampenLoopStatement
    (h : ThreeSphereStereographicVanKampenLoopStatement) :
    ThreeSphereLoopNullhomotopyStatement :=
  threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement h

/-- The stereographic-loop-to-full-loop route is the equatorial based-loop route. -/
theorem threeSphere_loopNullhomotopyStatement_of_stereographicVanKampenLoopStatement_eq :
    threeSphere_loopNullhomotopyStatement_of_stereographicVanKampenLoopStatement =
      (fun h : ThreeSphereStereographicVanKampenLoopStatement =>
        threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement
          (basepoint := threeSphere_equatorPoint) h) := by
  funext h
  apply Subsingleton.elim

/-- A stereographic Van Kampen loop proof supplies path-homotopy uniqueness on `S^3`. -/
theorem threeSphere_pathHomotopyStatement_of_stereographicVanKampenLoopStatement
    (h : ThreeSphereStereographicVanKampenLoopStatement) :
    ThreeSpherePathHomotopyStatement :=
  threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement h

/-- The stereographic-loop-to-path route is the equatorial based-loop route. -/
theorem threeSphere_pathHomotopyStatement_of_stereographicVanKampenLoopStatement_eq :
    threeSphere_pathHomotopyStatement_of_stereographicVanKampenLoopStatement =
      (fun h : ThreeSphereStereographicVanKampenLoopStatement =>
        (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement
          (basepoint := threeSphere_equatorPoint) h :
            ThreeSpherePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- A stereographic Van Kampen loop proof supplies path-quotient uniqueness on `S^3`. -/
theorem threeSphere_pathQuotientSubsingletonStatement_of_stereographicVanKampenLoopStatement
    (h : ThreeSphereStereographicVanKampenLoopStatement) :
    ThreeSpherePathQuotientSubsingletonStatement :=
  threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement h

/-- The stereographic-loop-to-path-quotient route is the equatorial based-loop route. -/
theorem threeSphere_pathQuotientSubsingletonStatement_of_stereographicVanKampenLoopStatement_eq :
    threeSphere_pathQuotientSubsingletonStatement_of_stereographicVanKampenLoopStatement =
      (fun h : ThreeSphereStereographicVanKampenLoopStatement =>
        (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement
          (basepoint := threeSphere_equatorPoint) h :
            ThreeSpherePathQuotientSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/-- A stereographic Van Kampen loop proof supplies fundamental-group triviality on `S^3`. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_stereographicVanKampenLoopStatement
    (h : ThreeSphereStereographicVanKampenLoopStatement) :
    ThreeSphereFundamentalGroupSubsingletonStatement :=
  threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement h

/-- The stereographic-loop-to-fundamental-group route is the equatorial based-loop route. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_stereographicVanKampenLoopStatement_eq :
    threeSphere_fundamentalGroupSubsingletonStatement_of_stereographicVanKampenLoopStatement =
      (fun h : ThreeSphereStereographicVanKampenLoopStatement =>
        (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement
          (basepoint := threeSphere_equatorPoint) h :
            ThreeSphereFundamentalGroupSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/-- A stereographic Van Kampen loop proof supplies the `π₁` formulation on `S^3`. -/
theorem threeSphere_piOneSubsingletonStatement_of_stereographicVanKampenLoopStatement
    (h : ThreeSphereStereographicVanKampenLoopStatement) :
    ThreeSpherePiOneSubsingletonStatement :=
  threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement h

/-- The stereographic-loop-to-`π₁` route is the equatorial based-loop route. -/
theorem threeSphere_piOneSubsingletonStatement_of_stereographicVanKampenLoopStatement_eq :
    threeSphere_piOneSubsingletonStatement_of_stereographicVanKampenLoopStatement =
      (fun h : ThreeSphereStereographicVanKampenLoopStatement =>
        (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement
          (basepoint := threeSphere_equatorPoint) h :
            ThreeSpherePiOneSubsingletonStatement)) := by
  funext h
  apply Subsingleton.elim

/-- North-pole based loop-nullhomotopy supplies path-homotopy uniqueness on `S^3`. -/
theorem threeSphere_pathHomotopyStatement_of_northPoleLoopNullhomotopyStatement
    (h : ThreeSphereNorthPoleLoopNullhomotopyStatement) :
    ThreeSpherePathHomotopyStatement :=
  threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement h

/-- The north-pole-to-path route is the generic based-loop route at the north pole. -/
theorem threeSphere_pathHomotopyStatement_of_northPoleLoopNullhomotopyStatement_eq :
    threeSphere_pathHomotopyStatement_of_northPoleLoopNullhomotopyStatement =
      (fun h : ThreeSphereNorthPoleLoopNullhomotopyStatement =>
        (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement h :
          ThreeSpherePathHomotopyStatement)) := by
  funext h
  apply Subsingleton.elim

/-- North-pole based loop-nullhomotopy supplies path-quotient uniqueness on `S^3`. -/
theorem threeSphere_pathQuotientSubsingletonStatement_of_northPoleLoopNullhomotopyStatement
    (h : ThreeSphereNorthPoleLoopNullhomotopyStatement) :
    ThreeSpherePathQuotientSubsingletonStatement :=
  threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement h

/-- The north-pole-to-path-quotient route factors through path-homotopy uniqueness. -/
theorem threeSphere_pathQuotientSubsingletonStatement_of_northPoleLoopNullhomotopyStatement_eq :
    threeSphere_pathQuotientSubsingletonStatement_of_northPoleLoopNullhomotopyStatement =
      (fun h : ThreeSphereNorthPoleLoopNullhomotopyStatement =>
        threeSphere_pathQuotientSubsingletonStatement_of_pathHomotopyStatement
          (threeSphere_pathHomotopyStatement_of_northPoleLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/-- North-pole based loop-nullhomotopy supplies fundamental-group triviality on `S^3`. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_northPoleLoopNullhomotopyStatement
    (h : ThreeSphereNorthPoleLoopNullhomotopyStatement) :
    ThreeSphereFundamentalGroupSubsingletonStatement :=
  threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement h

/-- The north-pole-to-fundamental-group route factors through full loop-nullhomotopy. -/
theorem threeSphere_fundamentalGroupSubsingletonStatement_of_northPoleLoopNullhomotopyStatement_eq :
    threeSphere_fundamentalGroupSubsingletonStatement_of_northPoleLoopNullhomotopyStatement =
      (fun h : ThreeSphereNorthPoleLoopNullhomotopyStatement =>
        threeSphere_fundamentalGroupSubsingletonStatement_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_northPoleLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/-- North-pole based loop-nullhomotopy supplies the `π₁` formulation on `S^3`. -/
theorem threeSphere_piOneSubsingletonStatement_of_northPoleLoopNullhomotopyStatement
    (h : ThreeSphereNorthPoleLoopNullhomotopyStatement) :
    ThreeSpherePiOneSubsingletonStatement :=
  threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement h

/-- The north-pole-to-`π₁` route factors through fundamental-group triviality. -/
theorem threeSphere_piOneSubsingletonStatement_of_northPoleLoopNullhomotopyStatement_eq :
    threeSphere_piOneSubsingletonStatement_of_northPoleLoopNullhomotopyStatement =
      (fun h : ThreeSphereNorthPoleLoopNullhomotopyStatement =>
        threeSphere_piOneSubsingletonStatement_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_northPoleLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/-- Full loop-nullhomotopy supplies the north-pole based loop-nullhomotopy obligation. -/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_loopNullhomotopyStatement
    (h : ThreeSphereLoopNullhomotopyStatement) :
    ThreeSphereNorthPoleLoopNullhomotopyStatement :=
  h threeSphere_northPole

/-- The full-loop-to-north-pole route is evaluation at the named north-pole point. -/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_loopNullhomotopyStatement_eq :
    threeSphere_northPoleLoopNullhomotopyStatement_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        h threeSphere_northPole) := by
  funext h
  apply Subsingleton.elim

/--
The north-pole based loop-nullhomotopy obligation is equivalent to the full
loop-nullhomotopy obligation for `S^3`.
-/
theorem threeSphere_northPoleLoopNullhomotopyStatement_iff_loopNullhomotopyStatement :
    ThreeSphereNorthPoleLoopNullhomotopyStatement ↔
      ThreeSphereLoopNullhomotopyStatement :=
  ⟨threeSphere_loopNullhomotopyStatement_of_northPoleLoopNullhomotopyStatement,
    threeSphere_northPoleLoopNullhomotopyStatement_of_loopNullhomotopyStatement⟩

/-- The north-pole/full-loop equivalence is the pair of the two named routes. -/
theorem threeSphere_northPoleLoopNullhomotopyStatement_iff_loopNullhomotopyStatement_eq :
    threeSphere_northPoleLoopNullhomotopyStatement_iff_loopNullhomotopyStatement =
      ⟨threeSphere_loopNullhomotopyStatement_of_northPoleLoopNullhomotopyStatement,
        threeSphere_northPoleLoopNullhomotopyStatement_of_loopNullhomotopyStatement⟩ := by
  apply Subsingleton.elim

/-- Path-homotopy uniqueness supplies the north-pole based loop-nullhomotopy obligation. -/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_pathHomotopyStatement
    (h : ThreeSpherePathHomotopyStatement) :
    ThreeSphereNorthPoleLoopNullhomotopyStatement :=
  threeSphere_northPoleLoopNullhomotopyStatement_of_loopNullhomotopyStatement
    (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement h)

/-- The path-to-north-pole route factors through full loop-nullhomotopy. -/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_pathHomotopyStatement_eq :
    threeSphere_northPoleLoopNullhomotopyStatement_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        threeSphere_northPoleLoopNullhomotopyStatement_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
Fundamental-group triviality supplies the north-pole based loop-nullhomotopy
obligation.
-/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
    (h : ThreeSphereFundamentalGroupSubsingletonStatement) :
    ThreeSphereNorthPoleLoopNullhomotopyStatement :=
  threeSphere_northPoleLoopNullhomotopyStatement_of_loopNullhomotopyStatement
    (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement h)

/-- The fundamental-group-to-north-pole route factors through full loop-nullhomotopy. -/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_northPoleLoopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement =
      (fun h : ThreeSphereFundamentalGroupSubsingletonStatement =>
        threeSphere_northPoleLoopNullhomotopyStatement_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/-- The `π₁` formulation supplies the north-pole based loop-nullhomotopy obligation. -/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_piOneSubsingletonStatement
    (h : ThreeSpherePiOneSubsingletonStatement) :
    ThreeSphereNorthPoleLoopNullhomotopyStatement :=
  threeSphere_northPoleLoopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
    (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement h)

/-- The `π₁`-to-north-pole route factors through fundamental-group triviality. -/
theorem threeSphere_northPoleLoopNullhomotopyStatement_of_piOneSubsingletonStatement_eq :
    threeSphere_northPoleLoopNullhomotopyStatement_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        threeSphere_northPoleLoopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement h)) := by
  funext h
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
The loop-nullhomotopy target-prerequisite route also agrees with the explicit
direct-simple prerequisite alias.
-/
theorem threeSphere_target_prerequisites_of_loopNullhomotopyStatement_direct_simple_route_eq :
    threeSphere_target_prerequisites_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
        threeSphere_target_prerequisites_of_simpleConnectedSpace) := by
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
The loop-nullhomotopy homotopy-prerequisite route also agrees with the explicit
direct-simple homotopy prerequisite alias.
-/
theorem threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement_direct_simple_route_eq :
    threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement =
      (fun h : ThreeSphereLoopNullhomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement h
        threeSphere_homotopy_prerequisites_of_simpleConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/--
Fundamental-group triviality supplies the full target prerequisite payload for
the standard sphere.
-/
theorem threeSphere_target_prerequisites_of_fundamentalGroupSubsingletonStatement
    (h : ThreeSphereFundamentalGroupSubsingletonStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement h
  exact threeSphere_target_prerequisites

/--
The fundamental-group target-prerequisite route is exactly the full target
payload after converting fundamental-group triviality to simple-connectedness.
-/
theorem threeSphere_target_prerequisites_of_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_target_prerequisites_of_fundamentalGroupSubsingletonStatement =
      (fun h : ThreeSphereFundamentalGroupSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement h
        threeSphere_target_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The fundamental-group target-prerequisite route also agrees with the explicit
direct-simple prerequisite alias.
-/
theorem threeSphere_target_prerequisites_of_fundamentalGroupSubsingletonStatement_direct_simple_route_eq :
    threeSphere_target_prerequisites_of_fundamentalGroupSubsingletonStatement =
      (fun h : ThreeSphereFundamentalGroupSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement h
        threeSphere_target_prerequisites_of_simpleConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/--
The fundamental-group target-prerequisite route agrees with the route that
first converts fundamental-group triviality to loop-nullhomotopy.
-/
theorem threeSphere_target_prerequisites_of_fundamentalGroupSubsingletonStatement_loop_route_eq :
    threeSphere_target_prerequisites_of_fundamentalGroupSubsingletonStatement =
      (fun h : ThreeSphereFundamentalGroupSubsingletonStatement =>
        threeSphere_target_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
Fundamental-group triviality also supplies the full homotopy-oriented
prerequisite payload for the standard sphere.
-/
theorem threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement
    (h : ThreeSphereFundamentalGroupSubsingletonStatement) :
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
    threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement h
  exact threeSphere_homotopy_prerequisites

/--
The fundamental-group homotopy-prerequisite route is exactly the full homotopy
payload after converting fundamental-group triviality to simple-connectedness.
-/
theorem threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement =
      (fun h : ThreeSphereFundamentalGroupSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement h
        threeSphere_homotopy_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The fundamental-group homotopy-prerequisite route also agrees with the explicit
direct-simple homotopy prerequisite alias.
-/
theorem threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement_direct_simple_route_eq :
    threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement =
      (fun h : ThreeSphereFundamentalGroupSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement h
        threeSphere_homotopy_prerequisites_of_simpleConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/--
The fundamental-group homotopy-prerequisite route agrees with the route that
first converts fundamental-group triviality to loop-nullhomotopy.
-/
theorem threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement_loop_route_eq :
    threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement =
      (fun h : ThreeSphereFundamentalGroupSubsingletonStatement =>
        threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The `π₁` subsingleton formulation supplies the full target prerequisite payload
for the standard sphere.
-/
theorem threeSphere_target_prerequisites_of_piOneSubsingletonStatement
    (h : ThreeSpherePiOneSubsingletonStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement h
  exact threeSphere_target_prerequisites

/--
The `π₁` target-prerequisite route is exactly the full target payload after
converting the `π₁` formulation to simple-connectedness.
-/
theorem threeSphere_target_prerequisites_of_piOneSubsingletonStatement_eq :
    threeSphere_target_prerequisites_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement h
        threeSphere_target_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The `π₁` target-prerequisite route also agrees with the explicit direct-simple
prerequisite alias.
-/
theorem threeSphere_target_prerequisites_of_piOneSubsingletonStatement_direct_simple_route_eq :
    threeSphere_target_prerequisites_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement h
        threeSphere_target_prerequisites_of_simpleConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/--
The `π₁` target-prerequisite route agrees with the route that first converts
`π₁` subsingletons to fundamental-group triviality.
-/
theorem threeSphere_target_prerequisites_of_piOneSubsingletonStatement_fundamentalGroup_route_eq :
    threeSphere_target_prerequisites_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        threeSphere_target_prerequisites_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement
            h)) := by
  funext h
  apply Subsingleton.elim

/--
The `π₁` target-prerequisite route also agrees with the route that first goes
through fundamental-group triviality and then loop-nullhomotopy.
-/
theorem threeSphere_target_prerequisites_of_piOneSubsingletonStatement_loop_route_eq :
    threeSphere_target_prerequisites_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        threeSphere_target_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The `π₁` subsingleton formulation also supplies the full homotopy-oriented
prerequisite payload for the standard sphere.
-/
theorem threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement
    (h : ThreeSpherePiOneSubsingletonStatement) :
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
    threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement h
  exact threeSphere_homotopy_prerequisites

/--
The `π₁` homotopy-prerequisite route is exactly the full homotopy payload after
converting the `π₁` formulation to simple-connectedness.
-/
theorem threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement_eq :
    threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement h
        threeSphere_homotopy_prerequisites) := by
  funext h
  apply Subsingleton.elim

/--
The `π₁` homotopy-prerequisite route also agrees with the explicit
direct-simple homotopy prerequisite alias.
-/
theorem threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement_direct_simple_route_eq :
    threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement h
        threeSphere_homotopy_prerequisites_of_simpleConnectedSpace) := by
  funext h
  apply Subsingleton.elim

/--
The `π₁` homotopy-prerequisite route agrees with the route that first converts
`π₁` subsingletons to fundamental-group triviality.
-/
theorem threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement_fundamentalGroup_route_eq :
    threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement
            h)) := by
  funext h
  apply Subsingleton.elim

/--
The `π₁` homotopy-prerequisite route also agrees with the route that first goes
through fundamental-group triviality and then loop-nullhomotopy.
-/
theorem threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement_loop_route_eq :
    threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement =
      (fun h : ThreeSpherePiOneSubsingletonStatement =>
        threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement h)) := by
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
The based-loop target-prerequisite route also agrees with the explicit
direct-simple prerequisite alias.
-/
theorem threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement_direct_simple_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h
        threeSphere_target_prerequisites_of_simpleConnectedSpace) := by
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
The based-loop homotopy-prerequisite route also agrees with the explicit
direct-simple homotopy prerequisite alias.
-/
theorem threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement_direct_simple_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement h
        threeSphere_homotopy_prerequisites_of_simpleConnectedSpace) := by
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
The direct based-loop target-prerequisite route agrees with the route through
fundamental-group triviality.
-/
theorem threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement_fundamentalGroup_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_target_prerequisites_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The direct based-loop target-prerequisite route agrees with the route through
the `π₁` formulation.
-/
theorem threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement_piOne_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_target_prerequisites_of_piOneSubsingletonStatement
          (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement h)) := by
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
The direct based-loop homotopy-prerequisite route agrees with the route through
fundamental-group triviality.
-/
theorem threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement_fundamentalGroup_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement
          (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The direct based-loop homotopy-prerequisite route agrees with the route through
the `π₁` formulation.
-/
theorem threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement_piOne_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement
          (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The north-pole based loop-nullhomotopy obligation supplies the full target
prerequisite payload for applying the project statement to the standard sphere.
-/
theorem threeSphere_target_prerequisites_of_northPoleLoopNullhomotopyStatement
    (h : ThreeSphereNorthPoleLoopNullhomotopyStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere :=
  threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement h

/--
The north-pole target-prerequisite route is the generic based-loop target route
specialized to the named north-pole point.
-/
theorem threeSphere_target_prerequisites_of_northPoleLoopNullhomotopyStatement_eq :
    threeSphere_target_prerequisites_of_northPoleLoopNullhomotopyStatement =
      (fun h : ThreeSphereNorthPoleLoopNullhomotopyStatement =>
        threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement h) := by
  funext h
  apply Subsingleton.elim

/--
The north-pole target-prerequisite route also agrees with first expanding to
the full loop-nullhomotopy obligation.
-/
theorem threeSphere_target_prerequisites_of_northPoleLoopNullhomotopyStatement_loop_route_eq :
    threeSphere_target_prerequisites_of_northPoleLoopNullhomotopyStatement =
      (fun h : ThreeSphereNorthPoleLoopNullhomotopyStatement =>
        threeSphere_target_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_northPoleLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The north-pole based loop-nullhomotopy obligation supplies the full
homotopy-oriented prerequisite payload for the standard sphere.
-/
theorem threeSphere_homotopy_prerequisites_of_northPoleLoopNullhomotopyStatement
    (h : ThreeSphereNorthPoleLoopNullhomotopyStatement) :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _locPath : LocPathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere :=
  threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement h

/--
The north-pole homotopy-prerequisite route is the generic based-loop homotopy
route specialized to the named north-pole point.
-/
theorem threeSphere_homotopy_prerequisites_of_northPoleLoopNullhomotopyStatement_eq :
    threeSphere_homotopy_prerequisites_of_northPoleLoopNullhomotopyStatement =
      (fun h : ThreeSphereNorthPoleLoopNullhomotopyStatement =>
        threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement h) := by
  funext h
  apply Subsingleton.elim

/--
The north-pole homotopy-prerequisite route also agrees with first expanding to
the full loop-nullhomotopy obligation.
-/
theorem threeSphere_homotopy_prerequisites_of_northPoleLoopNullhomotopyStatement_loop_route_eq :
    threeSphere_homotopy_prerequisites_of_northPoleLoopNullhomotopyStatement =
      (fun h : ThreeSphereNorthPoleLoopNullhomotopyStatement =>
        threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement
          (threeSphere_loopNullhomotopyStatement_of_northPoleLoopNullhomotopyStatement h)) := by
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
The path-homotopy target-prerequisite route also agrees with the explicit
direct-simple prerequisite alias.
-/
theorem threeSphere_target_prerequisites_of_pathHomotopyStatement_direct_simple_route_eq :
    threeSphere_target_prerequisites_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
        threeSphere_target_prerequisites_of_simpleConnectedSpace) := by
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
The path-homotopy homotopy-prerequisite route also agrees with the explicit
direct-simple homotopy prerequisite alias.
-/
theorem threeSphere_homotopy_prerequisites_of_pathHomotopyStatement_direct_simple_route_eq :
    threeSphere_homotopy_prerequisites_of_pathHomotopyStatement =
      (fun h : ThreeSpherePathHomotopyStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathHomotopyStatement h
        threeSphere_homotopy_prerequisites_of_simpleConnectedSpace) := by
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
The quotient-uniqueness target-prerequisite route also agrees with the explicit
direct-simple prerequisite alias.
-/
theorem threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement_direct_simple_route_eq :
    threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
        threeSphere_target_prerequisites_of_simpleConnectedSpace) := by
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
The quotient-uniqueness homotopy-prerequisite route also agrees with the
explicit direct-simple homotopy prerequisite alias.
-/
theorem threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement_direct_simple_route_eq :
    threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement =
      (fun h : ThreeSpherePathQuotientSubsingletonStatement =>
        letI : SimplyConnectedSpace ThreeSphere :=
          threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement h
        threeSphere_homotopy_prerequisites_of_simpleConnectedSpace) := by
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
The direct based-loop target-prerequisite route agrees with the route through
path-homotopy uniqueness.
-/
theorem threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement_path_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_target_prerequisites_of_pathHomotopyStatement
          (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The direct based-loop target-prerequisite route agrees with the route through
path-quotient uniqueness.
-/
theorem threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement_pathQuotient_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_target_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_target_prerequisites_of_pathQuotientSubsingletonStatement
          (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The direct based-loop homotopy-prerequisite route agrees with the route through
path-homotopy uniqueness.
-/
theorem threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement_path_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_homotopy_prerequisites_of_pathHomotopyStatement
          (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement h)) := by
  funext h
  apply Subsingleton.elim

/--
The direct based-loop homotopy-prerequisite route agrees with the route through
path-quotient uniqueness.
-/
theorem threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement_pathQuotient_route_eq
    (basepoint : ThreeSphere) :
    (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement h) =
      (fun h : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement
          (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement h)) := by
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
