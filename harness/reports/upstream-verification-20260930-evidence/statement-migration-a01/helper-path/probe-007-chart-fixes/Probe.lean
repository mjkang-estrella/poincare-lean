import Mathlib.Geometry.Manifold.PoincareConjecture
open scoped Manifold ContDiff
namespace Probe
abbrev E := EuclideanSpace ℝ (Fin 3)
variable {X : Type} [TopologicalSpace X] [Nonempty X]
variable (q : E)
variable [Nonempty ({q}ᶜ : Set E)]

theorem targetEmbedding : Topology.IsOpenEmbedding (Subtype.val : ({q}ᶜ : Set E) → E) :=
  isOpen_compl_singleton.isOpenEmbedding_subtypeVal

theorem sourceEmbedding (e : X ≃ₜ ({q}ᶜ : Set E)) :
    Topology.IsOpenEmbedding (fun p : X => (e p : E)) := by
  exact (targetEmbedding q).comp e.isOpenEmbedding

@[implicit_reducible]
noncomputable def sourceCharts (e : X ≃ₜ ({q}ᶜ : Set E)) : ChartedSpace E X :=
  (sourceEmbedding q e).singletonChartedSpace
@[implicit_reducible]
noncomputable def targetCharts : ChartedSpace E ({q}ᶜ : Set E) :=
  (targetEmbedding q).singletonChartedSpace

set_option backward.isDefEq.respectTransparency false
noncomputable def diffeo_exact (e : X ≃ₜ ({q}ᶜ : Set E)) :
    letI : ChartedSpace E X := sourceCharts q e
    letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
    X ≃ₘ⟮𝓡 3, 𝓡 3⟯ ({q}ᶜ : Set E) := by
  letI : ChartedSpace E X := sourceCharts q e
  letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
  let hsource := sourceEmbedding q e
  let htarget := targetEmbedding q
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := htarget) (by
          exact contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) hsource)
      contMDiff_invFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := hsource)
          ((contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) htarget).congr
            (fun x => by
              exact congrArg Subtype.val (e.apply_symm_apply x))) }

noncomputable def diffeo_unfold (e : X ≃ₜ ({q}ᶜ : Set E)) :
    letI : ChartedSpace E X := sourceCharts q e
    letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
    X ≃ₘ⟮𝓡 3, 𝓡 3⟯ ({q}ᶜ : Set E) := by
  letI : ChartedSpace E X := sourceCharts q e
  letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
  let hsource := sourceEmbedding q e
  let htarget := targetEmbedding q
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := htarget) (by
          simpa only [sourceCharts] using
            contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) hsource)
      contMDiff_invFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := hsource)
          ((contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) htarget).congr
            (fun x => by
              exact congrArg Subtype.val (e.apply_symm_apply x))) }

noncomputable def diffeo_change (e : X ≃ₜ ({q}ᶜ : Set E)) :
    letI : ChartedSpace E X := sourceCharts q e
    letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
    X ≃ₘ⟮𝓡 3, 𝓡 3⟯ ({q}ᶜ : Set E) := by
  letI : ChartedSpace E X := sourceCharts q e
  letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
  let hsource := sourceEmbedding q e
  let htarget := targetEmbedding q
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := htarget) (by
          change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p : X => (e p : E))
          exact contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) hsource)
      contMDiff_invFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := hsource)
          ((contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) htarget).congr
            (fun x => by
              exact congrArg Subtype.val (e.apply_symm_apply x))) }

noncomputable def diffeo_convert (e : X ≃ₜ ({q}ᶜ : Set E)) :
    letI : ChartedSpace E X := sourceCharts q e
    letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
    X ≃ₘ⟮𝓡 3, 𝓡 3⟯ ({q}ᶜ : Set E) := by
  letI : ChartedSpace E X := sourceCharts q e
  letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
  let hsource := sourceEmbedding q e
  let htarget := targetEmbedding q
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := htarget) (by
          convert contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) hsource using 1
          all_goals rfl)
      contMDiff_invFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := hsource)
          ((contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) htarget).congr
            (fun x => by
              exact congrArg Subtype.val (e.apply_symm_apply x))) }

noncomputable def diffeo_unfoldComp (e : X ≃ₜ ({q}ᶜ : Set E)) :
    letI : ChartedSpace E X := sourceCharts q e
    letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
    X ≃ₘ⟮𝓡 3, 𝓡 3⟯ ({q}ᶜ : Set E) := by
  letI : ChartedSpace E X := sourceCharts q e
  letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
  let hsource := sourceEmbedding q e
  let htarget := targetEmbedding q
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := htarget) (by
          simpa only [sourceCharts, Function.comp_def] using
            contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) hsource)
      contMDiff_invFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := hsource)
          ((contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) htarget).congr
            (fun x => by
              exact congrArg Subtype.val (e.apply_symm_apply x))) }

noncomputable def diffeo_congr (e : X ≃ₜ ({q}ᶜ : Set E)) :
    letI : ChartedSpace E X := sourceCharts q e
    letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
    X ≃ₘ⟮𝓡 3, 𝓡 3⟯ ({q}ᶜ : Set E) := by
  letI : ChartedSpace E X := sourceCharts q e
  letI : ChartedSpace E ({q}ᶜ : Set E) := targetCharts q
  let hsource := sourceEmbedding q e
  let htarget := targetEmbedding q
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := htarget) (by
          exact (contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) hsource).congr
            (fun p => rfl))
      contMDiff_invFun := by
        exact ContMDiff.of_comp_isOpenEmbedding (h' := hsource)
          ((contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞) htarget).congr
            (fun x => by
              exact congrArg Subtype.val (e.apply_symm_apply x))) }

end Probe
