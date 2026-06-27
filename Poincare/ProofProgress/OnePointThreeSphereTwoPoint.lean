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
The standard one-point compactification model two-puncture complement is
nonempty, path-connected, connected, and simply connected. This exposes the
topological core of the chart/path-loop payload without requiring consumers to
unpack the larger projection bundle.
-/
theorem onePoint_threeSpace_twoPointComplement_topology_package
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    Nonempty (({p} ∪ {q})ᶜ :
      Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  exact
    ⟨twoPointComplement_nonempty_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩ hqp,
      twoPointComplement_pathConnectedSpace_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩ hqp,
      twoPointComplement_connectedSpace_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩ hqp,
      twoPointComplement_simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩ hqp⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_topology_package`. -/
theorem onePoint_threeSpace_twoPointComplement_topology_package_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_topology_package =
      @Poincare.onePoint_threeSpace_twoPointComplement_topology_package :=
  rfl

/--
The explicit one-point-to-`ThreeSphere` two-puncture complement bridge carries
matching topology packages on the source and target models: nonemptiness,
path-connectedness, connectedness, and simple connectedness on both sides.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_topology_packages
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    Nonempty (({p} ∪ {q})ᶜ :
      Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      Nonempty
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere) ∧
      PathConnectedSpace
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere) ∧
      ConnectedSpace
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere) ∧
      SimplyConnectedSpace
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere) := by
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  rcases onePoint_threeSpace_twoPointComplement_topology_package hqp with
    ⟨hSourceNonempty, hSourcePath, hSourceConnected, hSourceSimply⟩
  exact
    ⟨hSourceNonempty, hSourcePath, hSourceConnected, hSourceSimply,
      threeSphere_twoPointComplement_nonempty hImage,
      threeSphere_twoPointComplement_pathConnectedSpace hImage,
      threeSphere_twoPointComplement_connectedSpace hImage,
      threeSphere_twoPointComplement_simplyConnectedSpace hImage⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_topology_packages`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_topology_packages_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_topology_packages =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_topology_packages :=
  rfl

/--
The explicit two-puncture complement bridge supplies path-component collapse
and concrete joined/path witnesses at the source endpoints, at their
forward-transported `ThreeSphere` endpoints, and at target endpoints transported
back to the one-point compactification complement.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_path_component_packages
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    pathComponent sourceBase = Set.univ ∧
      Joined sourceBase sourceTarget ∧
      Nonempty (Path sourceBase sourceTarget) ∧
      pathComponent (H sourceBase) = Set.univ ∧
      Joined (H sourceBase) (H sourceTarget) ∧
      Nonempty (Path (H sourceBase) (H sourceTarget)) ∧
      pathComponent (H.symm targetBase) = Set.univ ∧
      Joined (H.symm targetBase) (H.symm targetTarget) ∧
      Nonempty (Path (H.symm targetBase) (H.symm targetTarget)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  exact
    ⟨twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp sourceBase,
      twoPointComplement_joined_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp sourceBase sourceTarget,
      twoPointComplement_path_nonempty_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp sourceBase sourceTarget,
      threeSphere_twoPointComplement_pathComponent_eq_univ
        hImage (H sourceBase),
      threeSphere_twoPointComplement_path_nonempty
        hImage (H sourceBase) (H sourceTarget),
      threeSphere_twoPointComplement_path_nonempty
        hImage (H sourceBase) (H sourceTarget),
      twoPointComplement_pathComponent_eq_univ_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp (H.symm targetBase),
      twoPointComplement_joined_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp (H.symm targetBase) (H.symm targetTarget),
      twoPointComplement_path_nonempty_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp (H.symm targetBase) (H.symm targetTarget)⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_path_component_packages`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_path_component_packages_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_path_component_packages =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_path_component_packages :=
  rfl

/--
The explicit two-puncture complement bridge supplies concrete canonical paths
with endpoint equations, joined witnesses, and homotopy uniqueness at source
endpoints, forward-transported `ThreeSphere` endpoints, and target endpoints
transported back to the one-point compactification complement.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_packages
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    (∃ sourceCanonical : Path sourceBase sourceTarget,
      sourceCanonical 0 = sourceBase ∧ sourceCanonical 1 = sourceTarget ∧
        Joined sourceBase sourceTarget ∧
        (∀ η : Path sourceBase sourceTarget,
          Path.Homotopic sourceCanonical η)) ∧
      (∃ targetCanonical : Path (H sourceBase) (H sourceTarget),
        targetCanonical 0 = H sourceBase ∧
          targetCanonical 1 = H sourceTarget ∧
          Joined (H sourceBase) (H sourceTarget) ∧
          (∀ η : Path (H sourceBase) (H sourceTarget),
            Path.Homotopic targetCanonical η)) ∧
      (∃ inverseCanonical : Path (H.symm targetBase) (H.symm targetTarget),
        inverseCanonical 0 = H.symm targetBase ∧
          inverseCanonical 1 = H.symm targetTarget ∧
          Joined (H.symm targetBase) (H.symm targetTarget) ∧
          (∀ η : Path (H.symm targetBase) (H.symm targetTarget),
            Path.Homotopic inverseCanonical η)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  rcases
      twoPointComplement_exists_path_with_endpoints_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp sourceBase sourceTarget with
    ⟨sourceCanonical, hSourceStart, hSourceEnd, hSourceJoined⟩
  rcases
      threeSphere_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique
        hImage (H sourceBase) (H sourceTarget) with
    ⟨targetCanonical, hTargetStart, hTargetEnd, hTargetJoined,
      hTargetUnique⟩
  rcases
      twoPointComplement_exists_path_with_endpoints_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp (H.symm targetBase) (H.symm targetTarget) with
    ⟨inverseCanonical, hInverseStart, hInverseEnd, hInverseJoined⟩
  exact
    ⟨⟨sourceCanonical, hSourceStart, hSourceEnd, hSourceJoined,
        fun η =>
          twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
            (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
            ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
            hqp sourceCanonical η⟩,
      ⟨targetCanonical, hTargetStart, hTargetEnd, hTargetJoined,
        hTargetUnique⟩,
      ⟨inverseCanonical, hInverseStart, hInverseEnd, hInverseJoined,
        fun η =>
          twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
            (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
            ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
            hqp inverseCanonical η⟩⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_packages`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_packages_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_packages =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_packages :=
  rfl

/--
Canonical path packages across the explicit two-puncture complement bridge also
compare to arbitrary supplied paths by homotopy and by path-homotopy quotient
equality. This is the consumer-facing path payload for source endpoints,
forward-transported `ThreeSphere` endpoints, and target endpoints transported
back to the one-point compactification complement.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_payloads
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (sourcePath : Path sourceBase sourceTarget)
    {targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    (targetPath : Path targetBase targetTarget) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    (∃ sourceCanonical : Path sourceBase sourceTarget,
      sourceCanonical 0 = sourceBase ∧ sourceCanonical 1 = sourceTarget ∧
        Joined sourceBase sourceTarget ∧
        Path.Homotopic sourcePath sourceCanonical ∧
        (⟦sourcePath⟧ : Path.Homotopic.Quotient sourceBase sourceTarget) =
          ⟦sourceCanonical⟧ ∧
        (∀ η : Path sourceBase sourceTarget,
          Path.Homotopic sourceCanonical η)) ∧
      (∃ targetCanonical : Path (H sourceBase) (H sourceTarget),
        targetCanonical 0 = H sourceBase ∧
          targetCanonical 1 = H sourceTarget ∧
          Joined (H sourceBase) (H sourceTarget) ∧
          Path.Homotopic
            (sourcePath.map H.continuous)
            targetCanonical ∧
          (⟦sourcePath.map H.continuous⟧ :
            Path.Homotopic.Quotient (H sourceBase) (H sourceTarget)) =
            ⟦targetCanonical⟧ ∧
          (∀ η : Path (H sourceBase) (H sourceTarget),
            Path.Homotopic targetCanonical η)) ∧
      (∃ inverseCanonical : Path (H.symm targetBase) (H.symm targetTarget),
        inverseCanonical 0 = H.symm targetBase ∧
          inverseCanonical 1 = H.symm targetTarget ∧
          Joined (H.symm targetBase) (H.symm targetTarget) ∧
          Path.Homotopic
            (targetPath.map H.symm.continuous)
            inverseCanonical ∧
          (⟦targetPath.map H.symm.continuous⟧ :
            Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetTarget)) =
            ⟦inverseCanonical⟧ ∧
          (∀ η : Path (H.symm targetBase) (H.symm targetTarget),
            Path.Homotopic inverseCanonical η)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  rcases
      onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_packages
        hqp sourceBase sourceTarget targetBase targetTarget with
    ⟨⟨sourceCanonical, hSourceStart, hSourceEnd, hSourceJoined,
        hSourceUnique⟩,
      ⟨targetCanonical, hTargetStart, hTargetEnd, hTargetJoined,
        hTargetUnique⟩,
      ⟨inverseCanonical, hInverseStart, hInverseEnd, hInverseJoined,
        hInverseUnique⟩⟩
  have hSource : Path.Homotopic sourcePath sourceCanonical :=
    (hSourceUnique sourcePath).symm
  have hTarget :
      Path.Homotopic (sourcePath.map H.continuous) targetCanonical :=
    (hTargetUnique (sourcePath.map H.continuous)).symm
  have hInverse :
      Path.Homotopic (targetPath.map H.symm.continuous) inverseCanonical :=
    (hInverseUnique (targetPath.map H.symm.continuous)).symm
  exact
    ⟨⟨sourceCanonical, hSourceStart, hSourceEnd, hSourceJoined,
        hSource, Quotient.sound hSource, hSourceUnique⟩,
      ⟨targetCanonical, hTargetStart, hTargetEnd, hTargetJoined,
        hTarget, Quotient.sound hTarget, hTargetUnique⟩,
      ⟨inverseCanonical, hInverseStart, hInverseEnd, hInverseJoined,
        hInverse, Quotient.sound hInverse, hInverseUnique⟩⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_payloads`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_payloads_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_payloads =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_canonical_path_payloads :=
  rfl

/--
Based loops across the explicit two-puncture complement bridge carry endpoint
equations, nullhomotopies, and fundamental-group `fromPath` equalities, both
before and after forward/inverse transport.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_loop_payloads
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (sourceLoop : Path sourceBase sourceBase)
    {targetBase :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    (targetLoop : Path targetBase targetBase) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    (sourceLoop 0 = sourceBase ∧ sourceLoop 1 = sourceBase ∧
      Path.Homotopic sourceLoop (Path.refl sourceBase) ∧
      FundamentalGroup.fromPath
          (⟦sourceLoop⟧ :
            Path.Homotopic.Quotient sourceBase sourceBase) =
        FundamentalGroup.fromPath
          (⟦Path.refl sourceBase⟧ :
            Path.Homotopic.Quotient sourceBase sourceBase)) ∧
      ((sourceLoop.map H.continuous) 0 = H sourceBase ∧
        (sourceLoop.map H.continuous) 1 = H sourceBase ∧
        Path.Homotopic
          (sourceLoop.map H.continuous)
          (Path.refl (H sourceBase)) ∧
        FundamentalGroup.fromPath
            (⟦sourceLoop.map H.continuous⟧ :
              Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) =
          FundamentalGroup.fromPath
            (⟦Path.refl (H sourceBase)⟧ :
              Path.Homotopic.Quotient (H sourceBase) (H sourceBase))) ∧
      (targetLoop 0 = targetBase ∧ targetLoop 1 = targetBase ∧
        Path.Homotopic targetLoop (Path.refl targetBase) ∧
        FundamentalGroup.fromPath
            (⟦targetLoop⟧ :
              Path.Homotopic.Quotient targetBase targetBase) =
          FundamentalGroup.fromPath
            (⟦Path.refl targetBase⟧ :
              Path.Homotopic.Quotient targetBase targetBase)) ∧
      ((targetLoop.map H.symm.continuous) 0 = H.symm targetBase ∧
        (targetLoop.map H.symm.continuous) 1 = H.symm targetBase ∧
        Path.Homotopic
          (targetLoop.map H.symm.continuous)
          (Path.refl (H.symm targetBase)) ∧
        FundamentalGroup.fromPath
            (⟦targetLoop.map H.symm.continuous⟧ :
              Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) =
          FundamentalGroup.fromPath
            (⟦Path.refl (H.symm targetBase)⟧ :
              Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase))) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  have hSourceLoop :
      Path.Homotopic sourceLoop (Path.refl sourceBase) :=
    twoPointComplement_loop_nullhomotopic_of_homeomorph_to_onePoint_threeSpace
      (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
      ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
      hqp sourceBase sourceLoop
  have hSourceFromPath :
      FundamentalGroup.fromPath
          (⟦sourceLoop⟧ :
            Path.Homotopic.Quotient sourceBase sourceBase) =
        FundamentalGroup.fromPath
          (⟦Path.refl sourceBase⟧ :
            Path.Homotopic.Quotient sourceBase sourceBase) :=
    congrArg FundamentalGroup.fromPath (Quotient.sound hSourceLoop)
  have hTargetPayload :=
    threeSphere_twoPointComplement_loop_payload hImage targetBase targetLoop
  have hTargetLoop :
      Path.Homotopic targetLoop (Path.refl targetBase) :=
    hTargetPayload.2.2.1
  have hSourceMapped :
      Path.Homotopic
        (sourceLoop.map H.continuous)
        (Path.refl (H sourceBase)) := by
    simpa using hSourceLoop.map (⟨H, H.continuous⟩)
  have hTargetMapped :
      Path.Homotopic
        (targetLoop.map H.symm.continuous)
        (Path.refl (H.symm targetBase)) := by
    simpa using hTargetLoop.map (⟨H.symm, H.symm.continuous⟩)
  have hSourceMappedFromPath :
      FundamentalGroup.fromPath
          (⟦sourceLoop.map H.continuous⟧ :
            Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) =
        FundamentalGroup.fromPath
          (⟦Path.refl (H sourceBase)⟧ :
            Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) :=
    congrArg FundamentalGroup.fromPath (Quotient.sound hSourceMapped)
  have hTargetMappedFromPath :
      FundamentalGroup.fromPath
          (⟦targetLoop.map H.symm.continuous⟧ :
            Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) =
        FundamentalGroup.fromPath
          (⟦Path.refl (H.symm targetBase)⟧ :
            Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) :=
    congrArg FundamentalGroup.fromPath (Quotient.sound hTargetMapped)
  exact
    ⟨⟨Path.source sourceLoop, Path.target sourceLoop,
        hSourceLoop, hSourceFromPath⟩,
      ⟨Path.source (sourceLoop.map H.continuous),
        Path.target (sourceLoop.map H.continuous),
        hSourceMapped, hSourceMappedFromPath⟩,
      hTargetPayload,
      ⟨Path.source (targetLoop.map H.symm.continuous),
        Path.target (targetLoop.map H.symm.continuous),
        hTargetMapped, hTargetMappedFromPath⟩⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_loop_payloads`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_loop_payloads_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_loop_payloads =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_loop_payloads :=
  rfl

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

/--
The inverse of the explicit complement homeomorphism transports a target
standard `ThreeSphere` path and based loop back to concrete source paths, and
the one-point compactification complement supplies the punctured-Euclidean
chart/path-loop projection payload for those mapped-back paths.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_inverse_mapped_path_loop_source_chart_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere))
    (targetPath : Path targetBase targetTarget)
    (targetLoop : Path targetBase targetBase) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    ∃ sourcePath : Path (H.symm targetBase) (H.symm targetTarget),
      ∃ sourceLoop : Path (H.symm targetBase) (H.symm targetBase),
        sourcePath = targetPath.map H.symm.continuous ∧
          sourceLoop = targetLoop.map H.symm.continuous ∧
          ∃ puncture : EuclideanSpace ℝ (Fin 3),
            ∃ chart :
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
                  ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
              ∃ pathData :
                  PointedPathComponentPathData
                    (({p} ∪ {q})ᶜ :
                      Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                    (H.symm targetBase),
                ∃ endpointData :
                    PointedChosenPathEndpointData
                      (({p} ∪ {q})ᶜ :
                        Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                      (H.symm targetBase) (H.symm targetTarget),
                  ∃ canonicalPath :
                      Path (H.symm targetBase) (H.symm targetTarget),
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
                      pathData.path_to (H.symm targetTarget) = canonicalPath ∧
                      endpointData.path = canonicalPath ∧
                      canonicalPath 0 = H.symm targetBase ∧
                      canonicalPath 1 = H.symm targetTarget ∧
                      Joined (H.symm targetBase) (H.symm targetTarget) ∧
                      pathComponent (H.symm targetBase) = Set.univ ∧
                      Path.Homotopic sourcePath canonicalPath ∧
                      (⟦sourcePath⟧ :
                        Path.Homotopic.Quotient (H.symm targetBase)
                          (H.symm targetTarget)) =
                        ⟦canonicalPath⟧ ∧
                      (∀ η : Path (H.symm targetBase) (H.symm targetTarget),
                        Path.Homotopic canonicalPath η) ∧
                      Subsingleton
                        (Path.Homotopic.Quotient (H.symm targetBase)
                          (H.symm targetTarget)) ∧
                      sourceLoop 0 = H.symm targetBase ∧
                      sourceLoop 1 = H.symm targetBase ∧
                      Path.Homotopic sourceLoop
                        (Path.refl (H.symm targetBase)) ∧
                      FundamentalGroup.fromPath
                          (⟦sourceLoop⟧ :
                            Path.Homotopic.Quotient (H.symm targetBase)
                              (H.symm targetBase)) =
                        FundamentalGroup.fromPath
                          (⟦Path.refl (H.symm targetBase)⟧ :
                            Path.Homotopic.Quotient (H.symm targetBase)
                              (H.symm targetBase)) ∧
                      Subsingleton
                        (HomotopyGroup.Pi 1
                          (({p} ∪ {q})ᶜ :
                            Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                          (H.symm targetBase)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  let sourcePath : Path (H.symm targetBase) (H.symm targetTarget) :=
    targetPath.map H.symm.continuous
  let sourceLoop : Path (H.symm targetBase) (H.symm targetBase) :=
    targetLoop.map H.symm.continuous
  exact
    ⟨sourcePath, sourceLoop, rfl, rfl,
      onePoint_threeSpace_twoPointComplement_chart_path_loop_projection_bundle
        hqp (H.symm targetBase) (H.symm targetTarget) sourcePath sourceLoop⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_inverse_mapped_path_loop_source_chart_payload`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_inverse_mapped_path_loop_source_chart_payload_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_inverse_mapped_path_loop_source_chart_payload =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_inverse_mapped_path_loop_source_chart_payload :=
  rfl

/--
The explicit complement homeomorphism and its inverse recover mapped paths and
loops pointwise. This records the concrete round-trip equations needed when a
consumer transports a path/loop payload across the one-point-to-`ThreeSphere`
two-puncture identification.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_roundtrip_eval
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (sourcePath : Path sourceBase sourceTarget)
    (sourceLoop : Path sourceBase sourceBase)
    {targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    (targetPath : Path targetBase targetTarget)
    (targetLoop : Path targetBase targetBase) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    (∀ t, H.symm ((sourcePath.map H.continuous) t) = sourcePath t) ∧
      (∀ t, H.symm ((sourceLoop.map H.continuous) t) = sourceLoop t) ∧
      (∀ t, H ((targetPath.map H.symm.continuous) t) = targetPath t) ∧
      (∀ t, H ((targetLoop.map H.symm.continuous) t) = targetLoop t) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    change H.symm (H (sourcePath t)) = sourcePath t
    exact H.left_inv (sourcePath t)
  · intro t
    change H.symm (H (sourceLoop t)) = sourceLoop t
    exact H.left_inv (sourceLoop t)
  · intro t
    change H (H.symm (targetPath t)) = targetPath t
    exact H.right_inv (targetPath t)
  · intro t
    change H (H.symm (targetLoop t)) = targetLoop t
    exact H.right_inv (targetLoop t)

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_roundtrip_eval`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_roundtrip_eval_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_roundtrip_eval =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_roundtrip_eval :=
  rfl

/--
Path homotopies and based-loop homotopies are transported by the explicit
one-point-to-`ThreeSphere` two-puncture complement homeomorphism and by its
inverse. This is the homotopy-level bridge underlying the path/loop payload
transport theorems above.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_homotopy_transport
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    {sourcePath₀ sourcePath₁ : Path sourceBase sourceTarget}
    {sourceLoop₀ sourceLoop₁ : Path sourceBase sourceBase}
    {targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    {targetPath₀ targetPath₁ : Path targetBase targetTarget}
    {targetLoop₀ targetLoop₁ : Path targetBase targetBase}
    (hSourcePath : Path.Homotopic sourcePath₀ sourcePath₁)
    (hSourceLoop : Path.Homotopic sourceLoop₀ sourceLoop₁)
    (hTargetPath : Path.Homotopic targetPath₀ targetPath₁)
    (hTargetLoop : Path.Homotopic targetLoop₀ targetLoop₁) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    Path.Homotopic
        (sourcePath₀.map H.continuous)
        (sourcePath₁.map H.continuous) ∧
      Path.Homotopic
        (sourceLoop₀.map H.continuous)
        (sourceLoop₁.map H.continuous) ∧
      Path.Homotopic
        (targetPath₀.map H.symm.continuous)
        (targetPath₁.map H.symm.continuous) ∧
      Path.Homotopic
        (targetLoop₀.map H.symm.continuous)
        (targetLoop₁.map H.symm.continuous) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hSourcePath.map (⟨H, H.continuous⟩)
  · exact hSourceLoop.map (⟨H, H.continuous⟩)
  · exact hTargetPath.map (⟨H.symm, H.symm.continuous⟩)
  · exact hTargetLoop.map (⟨H.symm, H.symm.continuous⟩)

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_homotopy_transport`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_homotopy_transport_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_homotopy_transport =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_homotopy_transport :=
  rfl

/--
The explicit complement homeomorphism transports path-homotopy quotient classes
in both directions. This is the quotient-level form used by fundamental-group
and path-component consumers after paths and loops have crossed the
one-point-to-`ThreeSphere` two-puncture chart.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_quotient_transport
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    {sourcePath₀ sourcePath₁ : Path sourceBase sourceTarget}
    {sourceLoop₀ sourceLoop₁ : Path sourceBase sourceBase}
    {targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    {targetPath₀ targetPath₁ : Path targetBase targetTarget}
    {targetLoop₀ targetLoop₁ : Path targetBase targetBase}
    (hSourcePath : Path.Homotopic sourcePath₀ sourcePath₁)
    (hSourceLoop : Path.Homotopic sourceLoop₀ sourceLoop₁)
    (hTargetPath : Path.Homotopic targetPath₀ targetPath₁)
    (hTargetLoop : Path.Homotopic targetLoop₀ targetLoop₁) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    (⟦sourcePath₀.map H.continuous⟧ :
        Path.Homotopic.Quotient (H sourceBase) (H sourceTarget)) =
        ⟦sourcePath₁.map H.continuous⟧ ∧
      (⟦sourceLoop₀.map H.continuous⟧ :
        Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) =
        ⟦sourceLoop₁.map H.continuous⟧ ∧
      (⟦targetPath₀.map H.symm.continuous⟧ :
        Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetTarget)) =
        ⟦targetPath₁.map H.symm.continuous⟧ ∧
      (⟦targetLoop₀.map H.symm.continuous⟧ :
        Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) =
        ⟦targetLoop₁.map H.symm.continuous⟧ := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Quotient.sound (hSourcePath.map (⟨H, H.continuous⟩))
  · exact Quotient.sound (hSourceLoop.map (⟨H, H.continuous⟩))
  · exact Quotient.sound (hTargetPath.map (⟨H.symm, H.symm.continuous⟩))
  · exact Quotient.sound (hTargetLoop.map (⟨H.symm, H.symm.continuous⟩))

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_quotient_transport`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_quotient_transport_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_quotient_transport =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_path_loop_quotient_transport :=
  rfl

/--
Transported based-loop homotopies give equal fundamental-group elements on both
sides of the explicit one-point-to-`ThreeSphere` two-puncture complement
homeomorphism. This is the group-level consumer of the homotopy and quotient
transport bridges above.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_loop_fromPath_transport
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    {sourceLoop₀ sourceLoop₁ : Path sourceBase sourceBase}
    {targetBase :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    {targetLoop₀ targetLoop₁ : Path targetBase targetBase}
    (hSourceLoop : Path.Homotopic sourceLoop₀ sourceLoop₁)
    (hTargetLoop : Path.Homotopic targetLoop₀ targetLoop₁) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    FundamentalGroup.fromPath
        (⟦sourceLoop₀.map H.continuous⟧ :
          Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) =
      FundamentalGroup.fromPath
        (⟦sourceLoop₁.map H.continuous⟧ :
          Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) ∧
      FundamentalGroup.fromPath
          (⟦targetLoop₀.map H.symm.continuous⟧ :
            Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) =
        FundamentalGroup.fromPath
          (⟦targetLoop₁.map H.symm.continuous⟧ :
            Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  exact
    ⟨congrArg FundamentalGroup.fromPath
        (Quotient.sound (hSourceLoop.map (⟨H, H.continuous⟩))),
      congrArg FundamentalGroup.fromPath
        (Quotient.sound (hTargetLoop.map (⟨H.symm, H.symm.continuous⟩)))⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_loop_fromPath_transport`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_loop_fromPath_transport_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_loop_fromPath_transport =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_loop_fromPath_transport :=
  rfl

/--
Nullhomotopic based loops remain nullhomotopic after transport through the
explicit two-puncture complement homeomorphism and after transport back through
its inverse.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_loop_nullhomotopy_transport
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (sourceLoop : Path sourceBase sourceBase)
    {targetBase :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    (targetLoop : Path targetBase targetBase)
    (hSourceLoop : Path.Homotopic sourceLoop (Path.refl sourceBase))
    (hTargetLoop : Path.Homotopic targetLoop (Path.refl targetBase)) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    Path.Homotopic
        (sourceLoop.map H.continuous)
        (Path.refl (H sourceBase)) ∧
      Path.Homotopic
        (targetLoop.map H.symm.continuous)
        (Path.refl (H.symm targetBase)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  refine ⟨?_, ?_⟩
  · simpa using hSourceLoop.map (⟨H, H.continuous⟩)
  · simpa using hTargetLoop.map (⟨H.symm, H.symm.continuous⟩)

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_loop_nullhomotopy_transport`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_loop_nullhomotopy_transport_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_loop_nullhomotopy_transport =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_loop_nullhomotopy_transport :=
  rfl

/--
Transported nullhomotopic based loops represent the same fundamental-group
element as the constant loop at the transported basepoint.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_nullhomotopic_loop_fromPath_transport
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (sourceLoop : Path sourceBase sourceBase)
    {targetBase :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    (targetLoop : Path targetBase targetBase)
    (hSourceLoop : Path.Homotopic sourceLoop (Path.refl sourceBase))
    (hTargetLoop : Path.Homotopic targetLoop (Path.refl targetBase)) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    FundamentalGroup.fromPath
        (⟦sourceLoop.map H.continuous⟧ :
          Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) =
      FundamentalGroup.fromPath
        (⟦Path.refl (H sourceBase)⟧ :
          Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) ∧
      FundamentalGroup.fromPath
          (⟦targetLoop.map H.symm.continuous⟧ :
            Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) =
        FundamentalGroup.fromPath
          (⟦Path.refl (H.symm targetBase)⟧ :
            Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  have hSource :
      Path.Homotopic
        (sourceLoop.map H.continuous)
        (Path.refl (H sourceBase)) := by
    simpa using hSourceLoop.map (⟨H, H.continuous⟩)
  have hTarget :
      Path.Homotopic
        (targetLoop.map H.symm.continuous)
        (Path.refl (H.symm targetBase)) := by
    simpa using hTargetLoop.map (⟨H.symm, H.symm.continuous⟩)
  exact
    ⟨congrArg FundamentalGroup.fromPath (Quotient.sound hSource),
      congrArg FundamentalGroup.fromPath (Quotient.sound hTarget)⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_nullhomotopic_loop_fromPath_transport`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_nullhomotopic_loop_fromPath_transport_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_nullhomotopic_loop_fromPath_transport =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_nullhomotopic_loop_fromPath_transport :=
  rfl

/--
The chart/path-loop projection payloads on both sides of the explicit
two-puncture complement homeomorphism make transported based loops trivial in
the corresponding fundamental group. The source loop is transported forward to
the standard `ThreeSphere` complement, and the target loop is transported back
to the one-point compactification complement.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_mapped_loops_fromPath_eq_refl
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (sourceBase :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (sourceLoop : Path sourceBase sourceBase)
    (targetBase :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere))
    (targetLoop : Path targetBase targetBase) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    FundamentalGroup.fromPath
        (⟦sourceLoop.map H.continuous⟧ :
          Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) =
      FundamentalGroup.fromPath
        (⟦Path.refl (H sourceBase)⟧ :
          Path.Homotopic.Quotient (H sourceBase) (H sourceBase)) ∧
      FundamentalGroup.fromPath
          (⟦targetLoop.map H.symm.continuous⟧ :
            Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) =
        FundamentalGroup.fromPath
          (⟦Path.refl (H.symm targetBase)⟧ :
            Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetBase)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  rcases
      onePoint_threeSpace_twoPointComplement_chart_path_loop_projection_bundle
        hqp sourceBase sourceBase (Path.refl sourceBase) sourceLoop with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hSourceLoop, _, _⟩
  rcases
      threeSphere_twoPointComplement_chart_path_loop_projection_bundle
        hImage targetBase targetBase (Path.refl targetBase) targetLoop with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hTargetLoop, _, _⟩
  have hSourceMapped :
      Path.Homotopic
        (sourceLoop.map H.continuous)
        (Path.refl (H sourceBase)) := by
    simpa using hSourceLoop.map (⟨H, H.continuous⟩)
  have hTargetMapped :
      Path.Homotopic
        (targetLoop.map H.symm.continuous)
        (Path.refl (H.symm targetBase)) := by
    simpa using hTargetLoop.map (⟨H.symm, H.symm.continuous⟩)
  exact
    ⟨congrArg FundamentalGroup.fromPath (Quotient.sound hSourceMapped),
      congrArg FundamentalGroup.fromPath (Quotient.sound hTargetMapped)⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_mapped_loops_fromPath_eq_refl`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_mapped_loops_fromPath_eq_refl_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_mapped_loops_fromPath_eq_refl =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_mapped_loops_fromPath_eq_refl :=
  rfl

/--
The transported basepoints supplied by the explicit two-puncture complement
homeomorphism have subsingleton first homotopy groups on both sides. This
packages the source one-point and target `ThreeSphere` pi-one triviality
theorems at the exact transported basepoints used by the chart bridge.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_transport_piOne_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (sourceBase :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (targetBase :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    Subsingleton
        (HomotopyGroup.Pi 1
          (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
              {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
            Set ThreeSphere) (H sourceBase)) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          (H.symm targetBase)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  exact
    ⟨threeSphere_twoPointComplement_piOne_subsingleton hImage (H sourceBase),
      twoPointComplement_piOne_subsingleton_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp (H.symm targetBase)⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_transport_piOne_subsingleton`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_transport_piOne_subsingleton_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_transport_piOne_subsingleton =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_transport_piOne_subsingleton :=
  rfl

/--
The transported endpoints supplied by the explicit two-puncture complement
homeomorphism have subsingleton path-homotopy quotients on both sides. This is
the path-space counterpart of the transported-basepoint pi-one certificate.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_transport_pathQuotient_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    Subsingleton
        (Path.Homotopic.Quotient (H sourceBase) (H sourceTarget)) ∧
      Subsingleton
        (Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetTarget)) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  exact
    ⟨threeSphere_twoPointComplement_pathQuotient_subsingleton
        hImage (H sourceBase) (H sourceTarget),
      twoPointComplement_pathQuotient_subsingleton_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp (H.symm targetBase) (H.symm targetTarget)⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_transport_pathQuotient_subsingleton`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_transport_pathQuotient_subsingleton_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_transport_pathQuotient_subsingleton =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_transport_pathQuotient_subsingleton :=
  rfl

/--
Any two paths with matching endpoints remain homotopic after transport through
the explicit two-puncture complement homeomorphism, in either direction. This
packages the path-level consequence behind the transported path-quotient
subsingleton certificate.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (sourcePath₀ sourcePath₁ : Path sourceBase sourceTarget)
    {targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    (targetPath₀ targetPath₁ : Path targetBase targetTarget) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    Path.Homotopic
        (sourcePath₀.map H.continuous)
        (sourcePath₁.map H.continuous) ∧
      Path.Homotopic
        (targetPath₀.map H.symm.continuous)
        (targetPath₁.map H.symm.continuous) := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  let e : OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere :=
    Classical.choice onePoint_threeSpace_homeomorph_threeSphere
  have hImage : e q ≠ e p := by
    intro h
    exact hqp (e.injective h)
  exact
    ⟨threeSphere_twoPointComplement_paths_homotopic
        hImage (sourcePath₀.map H.continuous) (sourcePath₁.map H.continuous),
      twoPointComplement_paths_homotopic_of_homeomorph_to_onePoint_threeSpace
        (M := OnePoint (EuclideanSpace ℝ (Fin 3)))
        ⟨Homeomorph.refl (OnePoint (EuclideanSpace ℝ (Fin 3)))⟩
        hqp (targetPath₀.map H.symm.continuous)
          (targetPath₁.map H.symm.continuous)⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic :=
  rfl

/--
Transported paths with matching endpoints carry both their path homotopies and
the induced path-homotopy quotient equalities. This is the payload form of
`onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic`.
-/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {sourceBase sourceTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (sourcePath₀ sourcePath₁ : Path sourceBase sourceTarget)
    {targetBase targetTarget :
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)}
    (targetPath₀ targetPath₁ : Path targetBase targetTarget) :
    let H :=
      onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
        hqp
    Path.Homotopic
        (sourcePath₀.map H.continuous)
        (sourcePath₁.map H.continuous) ∧
      (⟦sourcePath₀.map H.continuous⟧ :
        Path.Homotopic.Quotient (H sourceBase) (H sourceTarget)) =
        ⟦sourcePath₁.map H.continuous⟧ ∧
      Path.Homotopic
        (targetPath₀.map H.symm.continuous)
        (targetPath₁.map H.symm.continuous) ∧
      (⟦targetPath₀.map H.symm.continuous⟧ :
        Path.Homotopic.Quotient (H.symm targetBase) (H.symm targetTarget)) =
        ⟦targetPath₁.map H.symm.continuous⟧ := by
  dsimp
  let H :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  rcases
      onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic
        hqp sourcePath₀ sourcePath₁ targetPath₀ targetPath₁ with
    ⟨hSource, hTarget⟩
  exact
    ⟨hSource, Quotient.sound hSource, hTarget, Quotient.sound hTarget⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic_payload`. -/
theorem onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic_payload_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic_payload =
      @Poincare.onePoint_threeSpace_twoPointComplement_homeomorph_transport_paths_homotopic_payload :=
  rfl

end Poincare
