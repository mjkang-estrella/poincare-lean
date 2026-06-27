import Poincare.TopologyExtraction
import Poincare.ProofProgress.TopologyExtractionPunctureTransport

namespace Poincare

/--
The named one-point compactification homeomorphism identifies the two-puncture
compactification complement with the corresponding two-puncture complement in
the project `ThreeSphere`.
-/
noncomputable def onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (_hqp : q ≠ p) :
    (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere) := by
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  exact e.subtype (fun x => by
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro hx hxImage
      rcases hxImage with hxp | hxq
      · exact hx (Or.inl (e.injective hxp))
      · exact hx (Or.inr (e.injective hxq))
    · intro hx hxSource
      rcases hxSource with hxp | hxq
      · exact hx (Or.inl (by rw [hxp]))
      · exact hx (Or.inr (by rw [hxq])))

/--
The two-puncture compactification complement is simply connected by transporting
it to the corresponding `ThreeSphere` two-puncture complement.
-/
theorem onePoint_threeSpace_twoPointComplement_simplyConnectedSpace_via_threeSphere
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    SimplyConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  letI : SimplyConnectedSpace (({e p} ∪ {e q})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_simplyConnectedSpace hImage
  exact
    (onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp).toHomotopyEquiv.simplyConnectedSpace

/--
The standard one-point compactification model two-puncture complement carries
the transported punctured-Euclidean chart together with the canonical path,
endpoint-data, homotopy quotient collapse, loop nullhomotopy, and `π₁`
collapse payload.
-/
theorem onePoint_threeSpace_twoPointComplement_chart_path_loop_projection_bundle
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint target :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart :
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                basepoint target,
            ∃ canonicalPath : Path basepoint target,
              (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                Nonempty
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
                PathConnectedSpace
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
                SimplyConnectedSpace
                  (({p} ∪ {q})ᶜ :
                    Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
                pathData.path_to target = canonicalPath ∧
                endpointData.path = canonicalPath ∧
                canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
                Joined basepoint target ∧
                pathComponent basepoint = Set.univ ∧
                Path.Homotopic chosenPath canonicalPath ∧
                (⟦chosenPath⟧ :
                  Path.Homotopic.Quotient basepoint target) =
                  ⟦canonicalPath⟧ ∧
                (∀ η : Path basepoint target,
                  Path.Homotopic canonicalPath η) ∧
                Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
                loop 0 = basepoint ∧ loop 1 = basepoint ∧
                Path.Homotopic loop (Path.refl basepoint) ∧
                FundamentalGroup.fromPath
                    (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
                  FundamentalGroup.fromPath
                    (⟦Path.refl basepoint⟧ :
                      Path.Homotopic.Quotient basepoint basepoint) ∧
                Subsingleton
                  (HomotopyGroup.Pi 1
                    (({p} ∪ {q})ᶜ :
                      Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint) :=
  twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_onePoint_threeSpace
    (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
    ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
    hqp basepoint target chosenPath loop

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_chart_path_loop_projection_bundle`. -/
theorem onePoint_threeSpace_twoPointComplement_chart_path_loop_projection_bundle_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_chart_path_loop_projection_bundle =
      @Poincare.onePoint_threeSpace_twoPointComplement_chart_path_loop_projection_bundle :=
  rfl

end Poincare
