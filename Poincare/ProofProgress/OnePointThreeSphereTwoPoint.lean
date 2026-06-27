import Poincare.TopologyExtraction
import Poincare.ProofProgress.TopologyExtractionPunctureTransport
import Poincare.ProofProgress.ThreeSphereTwoPointPiOne

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

/--
The one-point compactification two-puncture model exposes both its explicit
homeomorphism to the corresponding standard `ThreeSphere` two-puncture
complement and its transported punctured-Euclidean chart/path-loop projection
payload.
-/
theorem onePoint_threeSpace_twoPointComplement_threeSphere_homeomorph_and_chart_path_loop_projection_bundle
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint target :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    Nonempty
      ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere)) ∧
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
                      (⟦loop⟧ :
                        Path.Homotopic.Quotient basepoint basepoint) =
                    FundamentalGroup.fromPath
                      (⟦Path.refl basepoint⟧ :
                        Path.Homotopic.Quotient basepoint basepoint) ∧
                  Subsingleton
                    (HomotopyGroup.Pi 1
                      (({p} ∪ {q})ᶜ :
                        Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                      basepoint) := by
  exact
    ⟨⟨onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp⟩,
      onePoint_threeSpace_twoPointComplement_chart_path_loop_projection_bundle
        hqp basepoint target chosenPath loop⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_threeSphere_homeomorph_and_chart_path_loop_projection_bundle`. -/
theorem onePoint_threeSpace_twoPointComplement_threeSphere_homeomorph_and_chart_path_loop_projection_bundle_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_threeSphere_homeomorph_and_chart_path_loop_projection_bundle =
      @Poincare.onePoint_threeSpace_twoPointComplement_threeSphere_homeomorph_and_chart_path_loop_projection_bundle :=
  rfl

/--
The one-point compactification two-puncture model and the corresponding
standard `ThreeSphere` two-puncture model expose their punctured-Euclidean
chart/path-loop payloads together with the explicit homeomorphism between the
two complements.
-/
theorem onePoint_threeSpace_twoPointComplement_source_and_threeSphere_target_chart_path_loop_projection_bundle
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (sourcePath : Path sourceBase sourceTarget)
    (sourceLoop : Path sourceBase sourceBase)
    (targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere))
    (targetPath : Path targetBase targetTarget)
    (targetLoop : Path targetBase targetBase) :
    Nonempty
      ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere)) ∧
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        ∃ chart :
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
              ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
          ∃ pathData :
              PointedPathComponentPathData
                (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                sourceBase,
            ∃ endpointData :
                PointedChosenPathEndpointData
                  (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                  sourceBase sourceTarget,
              ∃ canonicalPath : Path sourceBase sourceTarget,
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
                  pathData.path_to sourceTarget = canonicalPath ∧
                  endpointData.path = canonicalPath ∧
                  canonicalPath 0 = sourceBase ∧
                  canonicalPath 1 = sourceTarget ∧
                  Joined sourceBase sourceTarget ∧
                  pathComponent sourceBase = Set.univ ∧
                  Path.Homotopic sourcePath canonicalPath ∧
                  (⟦sourcePath⟧ :
                    Path.Homotopic.Quotient sourceBase sourceTarget) =
                    ⟦canonicalPath⟧ ∧
                  (∀ η : Path sourceBase sourceTarget,
                    Path.Homotopic canonicalPath η) ∧
                  Subsingleton
                    (Path.Homotopic.Quotient sourceBase sourceTarget) ∧
                  sourceLoop 0 = sourceBase ∧
                  sourceLoop 1 = sourceBase ∧
                  Path.Homotopic sourceLoop (Path.refl sourceBase) ∧
                  FundamentalGroup.fromPath
                      (⟦sourceLoop⟧ :
                        Path.Homotopic.Quotient sourceBase sourceBase) =
                    FundamentalGroup.fromPath
                      (⟦Path.refl sourceBase⟧ :
                        Path.Homotopic.Quotient sourceBase sourceBase) ∧
                  Subsingleton
                    (HomotopyGroup.Pi 1
                      (({p} ∪ {q})ᶜ :
                        Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                      sourceBase)) ∧
      ∃ puncture : EuclideanSpace ℝ (Fin 3),
        ∃ chart :
            (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
              Set ThreeSphere) ≃ₜ
              ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
          ∃ pathData :
              PointedPathComponentPathData
                (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                    {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                  Set ThreeSphere) targetBase,
            ∃ endpointData :
                PointedChosenPathEndpointData
                  (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                      {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                    Set ThreeSphere) targetBase targetTarget,
              ∃ canonicalPath : Path targetBase targetTarget,
                (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                  Nonempty
                    (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                        {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                      Set ThreeSphere) ∧
                  PathConnectedSpace
                    (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                        {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                      Set ThreeSphere) ∧
                  SimplyConnectedSpace
                    (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                        {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                      Set ThreeSphere) ∧
                  pathData.path_to targetTarget = canonicalPath ∧
                  endpointData.path = canonicalPath ∧
                  canonicalPath 0 = targetBase ∧
                  canonicalPath 1 = targetTarget ∧
                  Joined targetBase targetTarget ∧
                  pathComponent targetBase = Set.univ ∧
                  Path.Homotopic targetPath canonicalPath ∧
                  (⟦targetPath⟧ :
                    Path.Homotopic.Quotient targetBase targetTarget) =
                    ⟦canonicalPath⟧ ∧
                  (∀ η : Path targetBase targetTarget,
                    Path.Homotopic canonicalPath η) ∧
                  Subsingleton
                    (Path.Homotopic.Quotient targetBase targetTarget) ∧
                  targetLoop 0 = targetBase ∧
                  targetLoop 1 = targetBase ∧
                  Path.Homotopic targetLoop (Path.refl targetBase) ∧
                  FundamentalGroup.fromPath
                      (⟦targetLoop⟧ :
                        Path.Homotopic.Quotient targetBase targetBase) =
                    FundamentalGroup.fromPath
                      (⟦Path.refl targetBase⟧ :
                        Path.Homotopic.Quotient targetBase targetBase) ∧
                  Subsingleton
                    (HomotopyGroup.Pi 1
                      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                        Set ThreeSphere) targetBase) := by
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  exact
    ⟨⟨onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp⟩,
      onePoint_threeSpace_twoPointComplement_chart_path_loop_projection_bundle
        hqp sourceBase sourceTarget sourcePath sourceLoop,
      threeSphere_twoPointComplement_chart_path_loop_projection_bundle
        hImage targetBase targetTarget targetPath targetLoop⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_source_and_threeSphere_target_chart_path_loop_projection_bundle`. -/
theorem onePoint_threeSpace_twoPointComplement_source_and_threeSphere_target_chart_path_loop_projection_bundle_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_source_and_threeSphere_target_chart_path_loop_projection_bundle =
      @Poincare.onePoint_threeSpace_twoPointComplement_source_and_threeSphere_target_chart_path_loop_projection_bundle :=
  rfl

/--
The explicit complement homeomorphism transports a source path and based loop
to concrete target paths, and the target standard `ThreeSphere` complement
then supplies the punctured-Euclidean chart/path-loop projection payload for
those mapped paths.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_mapped_path_loop_target_chart_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (sourcePath : Path sourceBase sourceTarget)
    (sourceLoop : Path sourceBase sourceBase) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    ∃ targetPath : Path (H sourceBase) (H sourceTarget),
      ∃ targetLoop : Path (H sourceBase) (H sourceBase),
        targetPath = sourcePath.map H.continuous ∧
          targetLoop = sourceLoop.map H.continuous ∧
          ∃ puncture : EuclideanSpace ℝ (Fin 3),
            ∃ chart :
                (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                    {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                  Set ThreeSphere) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
              ∃ pathData :
                  PointedPathComponentPathData
                    (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                        {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                      Set ThreeSphere) (H sourceBase),
                ∃ endpointData :
                    PointedChosenPathEndpointData
                      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                        Set ThreeSphere) (H sourceBase) (H sourceTarget),
                  ∃ canonicalPath : Path (H sourceBase) (H sourceTarget),
                    (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                      Nonempty
                        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                          Set ThreeSphere) ∧
                      PathConnectedSpace
                        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                          Set ThreeSphere) ∧
                      SimplyConnectedSpace
                        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                          Set ThreeSphere) ∧
                      pathData.path_to (H sourceTarget) = canonicalPath ∧
                      endpointData.path = canonicalPath ∧
                      canonicalPath 0 = H sourceBase ∧
                      canonicalPath 1 = H sourceTarget ∧
                      Joined (H sourceBase) (H sourceTarget) ∧
                      pathComponent (H sourceBase) = Set.univ ∧
                      Path.Homotopic targetPath canonicalPath ∧
                      (⟦targetPath⟧ :
                        Path.Homotopic.Quotient (H sourceBase)
                          (H sourceTarget)) =
                        ⟦canonicalPath⟧ ∧
                      (∀ η : Path (H sourceBase) (H sourceTarget),
                        Path.Homotopic canonicalPath η) ∧
                      Subsingleton
                        (Path.Homotopic.Quotient (H sourceBase)
                          (H sourceTarget)) ∧
                      targetLoop 0 = H sourceBase ∧
                      targetLoop 1 = H sourceBase ∧
                      Path.Homotopic targetLoop (Path.refl (H sourceBase)) ∧
                      FundamentalGroup.fromPath
                          (⟦targetLoop⟧ :
                            Path.Homotopic.Quotient (H sourceBase)
                              (H sourceBase)) =
                        FundamentalGroup.fromPath
                          (⟦Path.refl (H sourceBase)⟧ :
                            Path.Homotopic.Quotient (H sourceBase)
                              (H sourceBase)) ∧
                      Subsingleton
                        (HomotopyGroup.Pi 1
                          (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                              {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
                            Set ThreeSphere) (H sourceBase)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  let targetPath : Path (H sourceBase) (H sourceTarget) :=
    sourcePath.map H.continuous
  let targetLoop : Path (H sourceBase) (H sourceBase) :=
    sourceLoop.map H.continuous
  exact
    ⟨targetPath, targetLoop, rfl, rfl,
      threeSphere_twoPointComplement_chart_path_loop_projection_bundle
        hImage (H sourceBase) (H sourceTarget) targetPath targetLoop⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_mapped_path_loop_target_chart_payload`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_mapped_path_loop_target_chart_payload_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_mapped_path_loop_target_chart_payload =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_mapped_path_loop_target_chart_payload :=
  rfl

end Poincare
