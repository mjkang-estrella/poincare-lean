import Poincare.Statement
import Poincare.ProofProgress.TopologyExtractionPunctureTransport

namespace Poincare

/-- The two-puncture complement in the standard three-sphere is connected. -/
theorem threeSphere_twoPointComplement_connectedSpace
    {a b : ThreeSphere} (hab : b ≠ a) :
    ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  infer_instance

/-- The two-puncture complement in the standard three-sphere is nonempty. -/
theorem threeSphere_twoPointComplement_nonempty
    {a b : ThreeSphere} (hab : b ≠ a) :
    Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  infer_instance

/--
The standard three-sphere two-puncture complement is nonempty, path-connected,
connected, and simply connected. This packages the topological core used by the
path, loop, quotient, and `π₁` payloads below.
-/
theorem threeSphere_twoPointComplement_topology_package
    {a b : ThreeSphere} (hab : b ≠ a) :
    Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) := by
  exact
    ⟨threeSphere_twoPointComplement_nonempty hab,
      threeSphere_twoPointComplement_pathConnectedSpace hab,
      threeSphere_twoPointComplement_connectedSpace hab,
      threeSphere_twoPointComplement_simplyConnectedSpace hab⟩

/-- Theorem contract for `threeSphere_twoPointComplement_topology_package`. -/
theorem threeSphere_twoPointComplement_topology_package_eq :
    @Poincare.threeSphere_twoPointComplement_topology_package =
      @Poincare.threeSphere_twoPointComplement_topology_package :=
  rfl

/--
The standard three-sphere two-puncture complement carries a concrete
punctured-Euclidean chart. The chart lands in the complement of a named
Euclidean puncture, avoids that puncture pointwise, and carries the
nonempty/path-connected/simply-connected topology payload.
-/
theorem threeSphere_twoPointComplement_puncturedEuclidean_chart_package
    {a b : ThreeSphere} (hab : b ≠ a) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({a} ∪ {b})ᶜ : Set ThreeSphere) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ z, (chart z : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
          Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
          PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
          SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
  exists_puncture_homeomorph_twoPointComplement_puncturedEuclidean_topologyPayload
    (M := ThreeSphere)
    (homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere
      ⟨Homeomorph.refl ThreeSphere⟩)
    hab

/-- Theorem contract for `threeSphere_twoPointComplement_puncturedEuclidean_chart_package`. -/
theorem threeSphere_twoPointComplement_puncturedEuclidean_chart_package_eq :
    @Poincare.threeSphere_twoPointComplement_puncturedEuclidean_chart_package =
      @Poincare.threeSphere_twoPointComplement_puncturedEuclidean_chart_package :=
  rfl

/--
The standard three-sphere two-puncture complement carries a concrete
punctured-Euclidean chart together with the full topology payload used by the
recognition bridge.
-/
theorem threeSphere_twoPointComplement_puncturedEuclidean_fullChart_package
    {a b : ThreeSphere} (hab : b ≠ a) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({a} ∪ {b})ᶜ : Set ThreeSphere) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ z, (chart z : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
          Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
          PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
          ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
          SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) := by
  rcases threeSphere_twoPointComplement_topology_package hab with
    ⟨_, _, hConnected, _⟩
  rcases threeSphere_twoPointComplement_puncturedEuclidean_chart_package hab with
    ⟨puncture, chart, hAvoid, hNonempty, hPath, hSimply⟩
  exact
    ⟨puncture, chart, hAvoid, hNonempty, hPath, hConnected, hSimply⟩

/-- Theorem contract for `threeSphere_twoPointComplement_puncturedEuclidean_fullChart_package`. -/
theorem threeSphere_twoPointComplement_puncturedEuclidean_fullChart_package_eq :
    @Poincare.threeSphere_twoPointComplement_puncturedEuclidean_fullChart_package =
      @Poincare.threeSphere_twoPointComplement_puncturedEuclidean_fullChart_package :=
  rfl

/--
Every point of a standard three-sphere two-puncture complement lies in the
path component of any chosen basepoint.
-/
theorem threeSphere_twoPointComplement_pathComponent_eq_univ
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    pathComponent basepoint = Set.univ := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    exact PathConnectedSpace.joined basepoint z

/-- Any two points in a standard three-sphere two-puncture complement are joined by a path. -/
theorem threeSphere_twoPointComplement_path_nonempty
    {a b : ThreeSphere} (hab : b ≠ a) :
    ∀ (x y : (({a} ∪ {b})ᶜ : Set ThreeSphere)), Nonempty (Path x y) := by
  intro x y
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  exact PathConnectedSpace.joined x y

/--
The two-puncture complement in the standard three-sphere has trivial
fundamental group at every basepoint.
-/
theorem threeSphere_twoPointComplement_fundamentalGroup_subsingleton
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Subsingleton (FundamentalGroup (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  letI : SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_simplyConnectedSpace hab
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/--
The equivalent first homotopy group formulation of the two-puncture complement
triviality.
-/
theorem threeSphere_twoPointComplement_piOne_subsingleton
    {a b : ThreeSphere} (hab : b ≠ a)
    (x : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    Subsingleton (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) x) := by
  exact ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := (({a} ∪ {b})ᶜ : Set ThreeSphere)) (x := x)).subsingleton_congr).mpr
      (threeSphere_twoPointComplement_fundamentalGroup_subsingleton hab x)

/--
Every based loop in a standard three-sphere two-puncture complement is
null-homotopic.
-/
theorem threeSphere_twoPointComplement_loop_nullhomotopic
    {a b : ThreeSphere} (hab : b ≠ a) :
    ∀ (basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere))
      (γ : Path basepoint basepoint), Path.Homotopic γ (Path.refl basepoint) := by
  intro basepoint γ
  letI : SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_simplyConnectedSpace hab
  exact SimplyConnectedSpace.paths_homotopic γ (Path.refl basepoint)

/--
Every based loop in a standard three-sphere two-puncture complement carries its
endpoint equations, its null-homotopy, and the induced equality in the
fundamental group.
-/
theorem threeSphere_twoPointComplement_loop_payload
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (γ : Path basepoint basepoint) :
    γ 0 = basepoint ∧ γ 1 = basepoint ∧
      Path.Homotopic γ (Path.refl basepoint) ∧
      FundamentalGroup.fromPath
          (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint) =
        FundamentalGroup.fromPath
          (⟦Path.refl basepoint⟧ :
            Path.Homotopic.Quotient basepoint basepoint) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Path.source γ
  · exact Path.target γ
  · exact threeSphere_twoPointComplement_loop_nullhomotopic hab basepoint γ
  · exact congrArg FundamentalGroup.fromPath
      (Quotient.sound
        (threeSphere_twoPointComplement_loop_nullhomotopic hab basepoint γ))

/--
Any two paths with the same endpoints in a standard three-sphere two-puncture
complement are homotopic.
-/
theorem threeSphere_twoPointComplement_paths_homotopic
    {a b : ThreeSphere} (hab : b ≠ a) :
    ∀ {x y : (({a} ∪ {b})ᶜ : Set ThreeSphere)} (γ η : Path x y),
      Path.Homotopic γ η := by
  intro x y γ η
  letI : SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_simplyConnectedSpace hab
  exact SimplyConnectedSpace.paths_homotopic γ η

/--
Any two paths with the same endpoints in a standard three-sphere two-puncture
complement carry both the path homotopy and the induced equality of
path-homotopy quotient classes.
-/
theorem threeSphere_twoPointComplement_paths_homotopic_payload
    {a b : ThreeSphere} (hab : b ≠ a)
    {x y : (({a} ∪ {b})ᶜ : Set ThreeSphere)}
    (γ η : Path x y) :
    Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient x y) = ⟦η⟧ := by
  letI : SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_simplyConnectedSpace hab
  let h : Path.Homotopic γ η := SimplyConnectedSpace.paths_homotopic γ η
  exact ⟨h, Quotient.sound h⟩

/--
Every path-homotopy quotient in a standard three-sphere two-puncture complement
is a subsingleton.
-/
theorem threeSphere_twoPointComplement_pathQuotient_subsingleton
    {a b : ThreeSphere} (hab : b ≠ a) :
    ∀ (x y : (({a} ∪ {b})ᶜ : Set ThreeSphere)),
      Subsingleton (Path.Homotopic.Quotient x y) := by
  intro x y
  rw [subsingleton_iff]
  intro γ η
  induction γ using Quotient.inductionOn with
  | h γ =>
    induction η using Quotient.inductionOn with
    | h η =>
      exact Quotient.sound
        (threeSphere_twoPointComplement_paths_homotopic hab γ η)

/--
The standard three-sphere two-puncture complement supplies a concrete path
between any two selected points, with endpoint equations, the corresponding
`Joined` witness, and homotopy uniqueness among all paths with those endpoints.
-/
theorem threeSphere_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    ∃ canonicalPath : Path basepoint target,
      canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
        Joined basepoint target ∧
        ∀ η : Path basepoint target, Path.Homotopic canonicalPath η := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  let joined : Joined basepoint target :=
    PathConnectedSpace.joined basepoint target
  refine ⟨joined.somePath, ?_, ?_, joined, ?_⟩
  · exact Path.source joined.somePath
  · exact Path.target joined.somePath
  · intro η
    exact threeSphere_twoPointComplement_paths_homotopic hab joined.somePath η

/-- Theorem contract for `threeSphere_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique`. -/
theorem threeSphere_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique_eq :
    @Poincare.threeSphere_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique =
      @Poincare.threeSphere_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique :=
  rfl

/--
A compact model-level consumer for the standard three-sphere two-puncture
complement: any supplied path is homotopic to a canonical path with endpoint
equations, every path quotient collapses, every based loop is null-homotopic,
and the first homotopy group is trivial.
-/
theorem threeSphere_twoPointComplement_compact_path_loop_payload
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ canonicalPath : Path basepoint target,
      canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
        Joined basepoint target ∧
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
          (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases
      threeSphere_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique
        hab basepoint target with
    ⟨canonicalPath, canonicalSource, canonicalTarget, canonicalJoined,
      canonicalUnique⟩
  rcases
      threeSphere_twoPointComplement_paths_homotopic_payload
        hab chosenPath canonicalPath with
    ⟨chosenHomotopic, chosenQuotientEq⟩
  rcases threeSphere_twoPointComplement_loop_payload hab basepoint loop with
    ⟨loopSource, loopTarget, loopHomotopic, loopFromPath⟩
  exact
    ⟨canonicalPath, canonicalSource, canonicalTarget, canonicalJoined,
      chosenHomotopic, chosenQuotientEq, canonicalUnique,
      threeSphere_twoPointComplement_pathQuotient_subsingleton
        hab basepoint target,
      loopSource, loopTarget, loopHomotopic, loopFromPath,
      threeSphere_twoPointComplement_piOne_subsingleton hab basepoint⟩

/-- Theorem contract for `threeSphere_twoPointComplement_compact_path_loop_payload`. -/
theorem threeSphere_twoPointComplement_compact_path_loop_payload_eq :
    @Poincare.threeSphere_twoPointComplement_compact_path_loop_payload =
      @Poincare.threeSphere_twoPointComplement_compact_path_loop_payload :=
  rfl

/--
The standard three-sphere two-puncture complement supplies the same
path/loop-level topology certificate used by the one-point compactification
complement route: nonemptiness, global path-component control, a chosen path
with homotopy uniqueness, quotient collapse, loop nullhomotopy, and trivial
first homotopy group.
-/
theorem threeSphere_twoPointComplement_path_loop_topology_certificate
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      pathComponent basepoint = Set.univ ∧
      Joined basepoint target ∧
      (∃ canonicalPath : Path basepoint target,
        canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
          Joined basepoint target ∧
          ∀ η : Path basepoint target, Path.Homotopic canonicalPath η) ∧
      (∀ η : Path basepoint target,
        Path.Homotopic chosenPath η ∧
          (⟦chosenPath⟧ :
            Path.Homotopic.Quotient basepoint target) = ⟦η⟧) ∧
      Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
      loop 0 = basepoint ∧ loop 1 = basepoint ∧
      Path.Homotopic loop (Path.refl basepoint) ∧
      FundamentalGroup.fromPath
          (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
        FundamentalGroup.fromPath
          (⟦Path.refl basepoint⟧ :
            Path.Homotopic.Quotient basepoint basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    threeSphere_twoPointComplement_pathConnectedSpace hab
  let joined : Joined basepoint target := PathConnectedSpace.joined basepoint target
  rcases threeSphere_twoPointComplement_loop_payload hab basepoint loop with
    ⟨loopSource, loopTarget, loopHomotopic, loopFromPath⟩
  refine
    ⟨threeSphere_twoPointComplement_nonempty hab,
      threeSphere_twoPointComplement_pathComponent_eq_univ hab basepoint,
      joined, ?_, ?_, threeSphere_twoPointComplement_pathQuotient_subsingleton
        hab basepoint target,
      loopSource, loopTarget, loopHomotopic, loopFromPath,
      threeSphere_twoPointComplement_piOne_subsingleton hab basepoint⟩
  · refine ⟨joined.somePath, ?_, ?_, ?_, ?_⟩
    · exact Path.source joined.somePath
    · exact Path.target joined.somePath
    · exact joined
    · intro η
      exact threeSphere_twoPointComplement_paths_homotopic hab joined.somePath η
  · intro η
    exact threeSphere_twoPointComplement_paths_homotopic_payload hab chosenPath η

/-- Theorem contract for `threeSphere_twoPointComplement_path_loop_topology_certificate`. -/
theorem threeSphere_twoPointComplement_path_loop_topology_certificate_eq :
    @Poincare.threeSphere_twoPointComplement_path_loop_topology_certificate =
      @Poincare.threeSphere_twoPointComplement_path_loop_topology_certificate :=
  rfl

/--
The standard three-sphere two-puncture path/loop certificate together with the
full topology package for the complement.
-/
theorem threeSphere_twoPointComplement_fullTopology_path_loop_certificate
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
      pathComponent basepoint = Set.univ ∧
      Joined basepoint target ∧
      (∃ canonicalPath : Path basepoint target,
        canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
          Joined basepoint target ∧
          ∀ η : Path basepoint target, Path.Homotopic canonicalPath η) ∧
      (∀ η : Path basepoint target,
        Path.Homotopic chosenPath η ∧
          (⟦chosenPath⟧ :
            Path.Homotopic.Quotient basepoint target) = ⟦η⟧) ∧
      Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
      loop 0 = basepoint ∧ loop 1 = basepoint ∧
      Path.Homotopic loop (Path.refl basepoint) ∧
      FundamentalGroup.fromPath
          (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
        FundamentalGroup.fromPath
          (⟦Path.refl basepoint⟧ :
            Path.Homotopic.Quotient basepoint basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases threeSphere_twoPointComplement_topology_package hab with
    ⟨hNonempty, hPathConnected, hConnected, hSimplyConnected⟩
  rcases
      threeSphere_twoPointComplement_path_loop_topology_certificate
        hab basepoint target chosenPath loop with
    ⟨_, hComponent, hJoined, hCanonical, hChosen, hQuotientSubsingleton,
      hLoopSource, hLoopTarget, hLoopHomotopic, hLoopFromPath, hPiOne⟩
  exact
    ⟨hNonempty, hPathConnected, hConnected, hSimplyConnected, hComponent,
      hJoined, hCanonical, hChosen, hQuotientSubsingleton, hLoopSource,
      hLoopTarget, hLoopHomotopic, hLoopFromPath, hPiOne⟩

/-- Theorem contract for `threeSphere_twoPointComplement_fullTopology_path_loop_certificate`. -/
theorem threeSphere_twoPointComplement_fullTopology_path_loop_certificate_eq :
    @Poincare.threeSphere_twoPointComplement_fullTopology_path_loop_certificate =
      @Poincare.threeSphere_twoPointComplement_fullTopology_path_loop_certificate :=
  rfl

/--
The standard three-sphere two-puncture certificate projects to a concrete
chosen path, its endpoint equations, homotopy uniqueness, quotient collapse,
loop nullhomotopy, and trivial first homotopy group.
-/
theorem threeSphere_twoPointComplement_chosen_path_loop_projection_bundle
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ canonicalPath : Path basepoint target,
      Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
        pathComponent basepoint = Set.univ ∧
        canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
        Joined basepoint target ∧
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
          (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases
      threeSphere_twoPointComplement_path_loop_topology_certificate
        hab basepoint target chosenPath loop with
    ⟨nonemptyComplement, componentEq, _joined, canonicalPayload,
      chosenPathPayload, quotientSubsingleton, loopSource, loopTarget,
      loopHomotopic, loopFromPath, piOneSubsingleton⟩
  rcases canonicalPayload with
    ⟨canonicalPath, canonicalSource, canonicalTarget, canonicalJoined,
      canonicalUnique⟩
  rcases chosenPathPayload canonicalPath with
    ⟨chosenHomotopic, chosenQuotientEq⟩
  exact
    ⟨canonicalPath, nonemptyComplement, componentEq, canonicalSource,
      canonicalTarget, canonicalJoined, chosenHomotopic, chosenQuotientEq,
      canonicalUnique, quotientSubsingleton, loopSource, loopTarget,
      loopHomotopic, loopFromPath, piOneSubsingleton⟩

/-- Theorem contract for `threeSphere_twoPointComplement_chosen_path_loop_projection_bundle`. -/
theorem threeSphere_twoPointComplement_chosen_path_loop_projection_bundle_eq :
    @Poincare.threeSphere_twoPointComplement_chosen_path_loop_projection_bundle =
      @Poincare.threeSphere_twoPointComplement_chosen_path_loop_projection_bundle :=
  rfl

/--
The standard three-sphere two-puncture certificate projects to a concrete
chosen path while retaining the full topology package for the complement.
-/
theorem threeSphere_twoPointComplement_fullTopology_chosen_path_loop_projection_bundle
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ canonicalPath : Path basepoint target,
      Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
        PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
        ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
        SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
        pathComponent basepoint = Set.univ ∧
        canonicalPath 0 = basepoint ∧ canonicalPath 1 = target ∧
        Joined basepoint target ∧
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
          (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases
      threeSphere_twoPointComplement_fullTopology_path_loop_certificate
        hab basepoint target chosenPath loop with
    ⟨hNonempty, hPathConnected, hConnected, hSimplyConnected, hComponent,
      _hJoined, hCanonical, hChosen, hQuotientSubsingleton, hLoopSource,
      hLoopTarget, hLoopHomotopic, hLoopFromPath, hPiOne⟩
  rcases hCanonical with
    ⟨canonicalPath, hCanonicalSource, hCanonicalTarget, hCanonicalJoined,
      hCanonicalUnique⟩
  rcases hChosen canonicalPath with
    ⟨hChosenHomotopic, hChosenQuotient⟩
  exact
    ⟨canonicalPath, hNonempty, hPathConnected, hConnected, hSimplyConnected,
      hComponent, hCanonicalSource, hCanonicalTarget, hCanonicalJoined,
      hChosenHomotopic, hChosenQuotient, hCanonicalUnique,
      hQuotientSubsingleton, hLoopSource, hLoopTarget, hLoopHomotopic,
      hLoopFromPath, hPiOne⟩

/-- Theorem contract for `threeSphere_twoPointComplement_fullTopology_chosen_path_loop_projection_bundle`. -/
theorem threeSphere_twoPointComplement_fullTopology_chosen_path_loop_projection_bundle_eq :
    @Poincare.threeSphere_twoPointComplement_fullTopology_chosen_path_loop_projection_bundle =
      @Poincare.threeSphere_twoPointComplement_fullTopology_chosen_path_loop_projection_bundle :=
  rfl

/--
The standard `ThreeSphere` two-puncture complement carries the transported
punctured-Euclidean chart together with the same canonical path, endpoint-data,
homotopy quotient, loop nullhomotopy, and `π₁` collapse payload used by the
recognition route.
-/
theorem threeSphere_twoPointComplement_chart_path_loop_projection_bundle
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({a} ∪ {b})ᶜ : Set ThreeSphere) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData
              (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint target,
            ∃ canonicalPath : Path basepoint target,
              (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
                PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
                SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
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
                    (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) :=
  twoPointComplement_chart_path_loop_projection_bundle_of_homeomorph_to_threeSphere
    (M := ThreeSphere) ⟨Homeomorph.refl ThreeSphere⟩ hab
    basepoint target chosenPath loop

/-- Theorem contract for `threeSphere_twoPointComplement_chart_path_loop_projection_bundle`. -/
theorem threeSphere_twoPointComplement_chart_path_loop_projection_bundle_eq :
    @Poincare.threeSphere_twoPointComplement_chart_path_loop_projection_bundle =
      @Poincare.threeSphere_twoPointComplement_chart_path_loop_projection_bundle :=
  rfl

/--
The standard `ThreeSphere` two-puncture chart/path/loop projection bundle with
the full chart topology payload, including connectedness of the complement.
-/
theorem threeSphere_twoPointComplement_fullChart_path_loop_projection_bundle
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({a} ∪ {b})ᶜ : Set ThreeSphere) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData
              (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint target,
            ∃ canonicalPath : Path basepoint target,
              (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
                PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
                ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
                SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
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
                    (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases threeSphere_twoPointComplement_topology_package hab with
    ⟨_, _, hConnected, _⟩
  rcases
      threeSphere_twoPointComplement_chart_path_loop_projection_bundle
        hab basepoint target chosenPath loop with
    ⟨puncture, chart, pathData, endpointData, canonicalPath, hAvoid,
      hNonempty, hPath, hSimply, hPathData, hEndpointData, hCanonicalSource,
      hCanonicalTarget, hJoined, hComponent, hChosenHomotopic,
      hChosenQuotient, hCanonicalUnique, hQuotientSubsingleton, hLoopSource,
      hLoopTarget, hLoopHomotopic, hLoopFromPath, hPiOne⟩
  exact
    ⟨puncture, chart, pathData, endpointData, canonicalPath, hAvoid,
      hNonempty, hPath, hConnected, hSimply, hPathData, hEndpointData,
      hCanonicalSource, hCanonicalTarget, hJoined, hComponent,
      hChosenHomotopic, hChosenQuotient, hCanonicalUnique,
      hQuotientSubsingleton, hLoopSource, hLoopTarget, hLoopHomotopic,
      hLoopFromPath, hPiOne⟩

/-- Theorem contract for `threeSphere_twoPointComplement_fullChart_path_loop_projection_bundle`. -/
theorem threeSphere_twoPointComplement_fullChart_path_loop_projection_bundle_eq :
    @Poincare.threeSphere_twoPointComplement_fullChart_path_loop_projection_bundle =
      @Poincare.threeSphere_twoPointComplement_fullChart_path_loop_projection_bundle :=
  rfl

/--
The standard `ThreeSphere` two-puncture complement exposes its full
punctured-Euclidean chart together with endpoint-level collapse data. This is
the path/`π₁` recognition payload that does not require a chosen path or loop.
-/
theorem threeSphere_twoPointComplement_fullChart_endpoint_collapse_package
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere)) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({a} ∪ {b})ᶜ : Set ThreeSphere) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
          Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
          PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
          ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
          SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
          pathComponent basepoint = Set.univ ∧
          Joined basepoint target ∧
          Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
          Subsingleton
            (HomotopyGroup.Pi 1 (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases threeSphere_twoPointComplement_puncturedEuclidean_fullChart_package hab with
    ⟨puncture, chart, hAvoid, hNonempty, hPathConnected, hConnected,
      hSimplyConnected⟩
  letI : PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) :=
    hPathConnected
  exact
    ⟨puncture, chart, hAvoid, hNonempty, hPathConnected, hConnected,
      hSimplyConnected, threeSphere_twoPointComplement_pathComponent_eq_univ
        hab basepoint, PathConnectedSpace.joined basepoint target,
      threeSphere_twoPointComplement_pathQuotient_subsingleton
        hab basepoint target,
      threeSphere_twoPointComplement_piOne_subsingleton hab basepoint⟩

/-- Theorem contract for `threeSphere_twoPointComplement_fullChart_endpoint_collapse_package`. -/
theorem threeSphere_twoPointComplement_fullChart_endpoint_collapse_package_eq :
    @Poincare.threeSphere_twoPointComplement_fullChart_endpoint_collapse_package =
      @Poincare.threeSphere_twoPointComplement_fullChart_endpoint_collapse_package :=
  rfl

/--
The standard `ThreeSphere` two-puncture complement exposes its full
punctured-Euclidean chart together with a canonical endpoint path, homotopy
uniqueness for that canonical path, and collapse of any supplied based loop.
This is the canonical-path version of the full chart endpoint package, before
an arbitrary chosen path is supplied by a downstream consumer.
-/
theorem threeSphere_twoPointComplement_fullChart_canonicalPath_loopCollapse_package
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (loop : Path basepoint basepoint) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({a} ∪ {b})ᶜ : Set ThreeSphere) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ canonicalPath : Path basepoint target,
          (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
            Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
            PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
            ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
            SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
            pathComponent basepoint = Set.univ ∧
            canonicalPath 0 = basepoint ∧
            canonicalPath 1 = target ∧
            Joined basepoint target ∧
            (∀ η : Path basepoint target,
              Path.Homotopic canonicalPath η) ∧
            Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
            loop 0 = basepoint ∧
            loop 1 = basepoint ∧
            Path.Homotopic loop (Path.refl basepoint) ∧
            FundamentalGroup.fromPath
                (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
              FundamentalGroup.fromPath
                (⟦Path.refl basepoint⟧ :
                  Path.Homotopic.Quotient basepoint basepoint) ∧
            Subsingleton
              (HomotopyGroup.Pi 1
                (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases
      threeSphere_twoPointComplement_fullChart_endpoint_collapse_package
        hab basepoint target with
    ⟨puncture, chart, hAvoid, hNonempty, hPathConnected, hConnected,
      hSimplyConnected, hComponent, _hJoined, hQuotient, hPiOne⟩
  rcases
      threeSphere_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique
        hab basepoint target with
    ⟨canonicalPath, hCanonicalSource, hCanonicalTarget, hCanonicalJoined,
      hCanonicalUnique⟩
  rcases threeSphere_twoPointComplement_loop_payload hab basepoint loop with
    ⟨hLoopSource, hLoopTarget, hLoopHomotopic, hLoopFromPath⟩
  exact
    ⟨puncture, chart, canonicalPath, hAvoid, hNonempty, hPathConnected,
      hConnected, hSimplyConnected, hComponent, hCanonicalSource,
      hCanonicalTarget, hCanonicalJoined, hCanonicalUnique, hQuotient,
      hLoopSource, hLoopTarget, hLoopHomotopic, hLoopFromPath, hPiOne⟩

/-- Theorem contract for
`threeSphere_twoPointComplement_fullChart_canonicalPath_loopCollapse_package`. -/
theorem threeSphere_twoPointComplement_fullChart_canonicalPath_loopCollapse_package_eq :
    @Poincare.threeSphere_twoPointComplement_fullChart_canonicalPath_loopCollapse_package =
      @Poincare.threeSphere_twoPointComplement_fullChart_canonicalPath_loopCollapse_package :=
  rfl

/--
The standard `ThreeSphere` two-puncture complement exposes its full
punctured-Euclidean chart, the concrete path-component and endpoint-data
objects selecting a canonical endpoint path, homotopy uniqueness for that path,
and collapse of any supplied based loop. This is the endpoint-data version of
the canonical full-chart loop package, still before an arbitrary chosen path is
supplied by a downstream consumer.
-/
theorem threeSphere_twoPointComplement_fullChart_endpointData_loopCollapse_package
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (loop : Path basepoint basepoint) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({a} ∪ {b})ᶜ : Set ThreeSphere) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData
              (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint target,
            ∃ canonicalPath : Path basepoint target,
              (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
                Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
                PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
                ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
                SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
                pathData.path_to target = canonicalPath ∧
                endpointData.path = canonicalPath ∧
                canonicalPath 0 = basepoint ∧
                canonicalPath 1 = target ∧
                Joined basepoint target ∧
                pathComponent basepoint = Set.univ ∧
                (∀ η : Path basepoint target,
                  Path.Homotopic canonicalPath η) ∧
                Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
                loop 0 = basepoint ∧
                loop 1 = basepoint ∧
                Path.Homotopic loop (Path.refl basepoint) ∧
                FundamentalGroup.fromPath
                    (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
                  FundamentalGroup.fromPath
                    (⟦Path.refl basepoint⟧ :
                      Path.Homotopic.Quotient basepoint basepoint) ∧
                Subsingleton
                  (HomotopyGroup.Pi 1
                    (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases
      threeSphere_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique
        hab basepoint target with
    ⟨seedPath, _seedSource, _seedTarget, _seedJoined, _seedUnique⟩
  rcases
      threeSphere_twoPointComplement_fullChart_path_loop_projection_bundle
        hab basepoint target seedPath loop with
    ⟨puncture, chart, pathData, endpointData, canonicalPath, hAvoid,
      hNonempty, hPathConnected, hConnected, hSimplyConnected, hPathData,
      hEndpointData, hCanonicalSource, hCanonicalTarget, hJoined, hComponent,
      _hChosenHomotopic, _hChosenQuotient, hCanonicalUnique,
      hQuotientSubsingleton, hLoopSource, hLoopTarget, hLoopHomotopic,
      hLoopFromPath, hPiOne⟩
  exact
    ⟨puncture, chart, pathData, endpointData, canonicalPath, hAvoid,
      hNonempty, hPathConnected, hConnected, hSimplyConnected, hPathData,
      hEndpointData, hCanonicalSource, hCanonicalTarget, hJoined, hComponent,
      hCanonicalUnique, hQuotientSubsingleton, hLoopSource, hLoopTarget,
      hLoopHomotopic, hLoopFromPath, hPiOne⟩

/-- Theorem contract for
`threeSphere_twoPointComplement_fullChart_endpointData_loopCollapse_package`. -/
theorem threeSphere_twoPointComplement_fullChart_endpointData_loopCollapse_package_eq :
    @Poincare.threeSphere_twoPointComplement_fullChart_endpointData_loopCollapse_package =
      @Poincare.threeSphere_twoPointComplement_fullChart_endpointData_loopCollapse_package :=
  rfl

/--
The endpoint-data path selected by the standard `ThreeSphere` two-puncture
full-chart package is coherent with the path-component selector and carries
the arbitrary chosen-path and loop-collapse payloads directly. Downstream
recognition code can consume `endpointData.path` without first rewriting
through an existential canonical path.
-/
theorem threeSphere_twoPointComplement_fullChart_endpointData_pathCoherence_loopCollapse_package
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({a} ∪ {b})ᶜ : Set ThreeSphere) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData
              (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint target,
            (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
              Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
              PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
              ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
              SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
              pathData.path_to target = endpointData.path ∧
              endpointData.path 0 = basepoint ∧
              endpointData.path 1 = target ∧
              Joined basepoint target ∧
              pathComponent basepoint = Set.univ ∧
              Path.Homotopic chosenPath endpointData.path ∧
              (⟦chosenPath⟧ :
                Path.Homotopic.Quotient basepoint target) =
                ⟦endpointData.path⟧ ∧
              (∀ η : Path basepoint target,
                Path.Homotopic endpointData.path η) ∧
              Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
              loop 0 = basepoint ∧
              loop 1 = basepoint ∧
              Path.Homotopic loop (Path.refl basepoint) ∧
              FundamentalGroup.fromPath
                  (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
                FundamentalGroup.fromPath
                  (⟦Path.refl basepoint⟧ :
                    Path.Homotopic.Quotient basepoint basepoint) ∧
              Subsingleton
                (HomotopyGroup.Pi 1
                  (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases
      threeSphere_twoPointComplement_fullChart_path_loop_projection_bundle
        hab basepoint target chosenPath loop with
    ⟨puncture, chart, pathData, endpointData, canonicalPath, hAvoid,
      hNonempty, hPathConnected, hConnected, hSimplyConnected, hPathData,
      hEndpointData, hCanonicalSource, hCanonicalTarget, hJoined, hComponent,
      hChosenHomotopic, hChosenQuotient, hCanonicalUnique,
      hQuotientSubsingleton, hLoopSource, hLoopTarget, hLoopHomotopic,
      hLoopFromPath, hPiOne⟩
  exact
    ⟨puncture, chart, pathData, endpointData, hAvoid, hNonempty,
      hPathConnected, hConnected, hSimplyConnected,
      hPathData.trans hEndpointData.symm,
      by simpa [hEndpointData] using hCanonicalSource,
      by simpa [hEndpointData] using hCanonicalTarget, hJoined, hComponent,
      by simpa [hEndpointData] using hChosenHomotopic,
      by simpa [hEndpointData] using hChosenQuotient,
      by
        intro η
        simpa [hEndpointData] using hCanonicalUnique η,
      hQuotientSubsingleton, hLoopSource, hLoopTarget, hLoopHomotopic,
      hLoopFromPath, hPiOne⟩

/-- Theorem contract for
`threeSphere_twoPointComplement_fullChart_endpointData_pathCoherence_loopCollapse_package`. -/
theorem threeSphere_twoPointComplement_fullChart_endpointData_pathCoherence_loopCollapse_package_eq :
    @Poincare.threeSphere_twoPointComplement_fullChart_endpointData_pathCoherence_loopCollapse_package =
      @Poincare.threeSphere_twoPointComplement_fullChart_endpointData_pathCoherence_loopCollapse_package :=
  rfl

/--
The endpoint-data selector in the standard `ThreeSphere` two-puncture
full-chart package directly supplies a path with endpoint equations, homotopy
uniqueness, quotient collapse, and loop collapse. This is the no-arbitrary-path
consumer form of the endpoint-data loop package.
-/
theorem threeSphere_twoPointComplement_fullChart_endpointData_direct_loopCollapse_package
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (loop : Path basepoint basepoint) :
    ∃ puncture : EuclideanSpace ℝ (Fin 3),
      ∃ chart : (({a} ∪ {b})ᶜ : Set ThreeSphere) ≃ₜ
          ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
        ∃ pathData :
            PointedPathComponentPathData
              (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint,
          ∃ endpointData :
              PointedChosenPathEndpointData
                (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint target,
            (∀ w, (chart w : EuclideanSpace ℝ (Fin 3)) ≠ puncture) ∧
              Nonempty (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
              PathConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
              ConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
              SimplyConnectedSpace (({a} ∪ {b})ᶜ : Set ThreeSphere) ∧
              pathData.path_to target = endpointData.path ∧
              endpointData.path 0 = basepoint ∧
              endpointData.path 1 = target ∧
              Joined basepoint target ∧
              pathComponent basepoint = Set.univ ∧
              (∀ η : Path basepoint target,
                Path.Homotopic endpointData.path η) ∧
              Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
              loop 0 = basepoint ∧
              loop 1 = basepoint ∧
              Path.Homotopic loop (Path.refl basepoint) ∧
              FundamentalGroup.fromPath
                  (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
                FundamentalGroup.fromPath
                  (⟦Path.refl basepoint⟧ :
                    Path.Homotopic.Quotient basepoint basepoint) ∧
              Subsingleton
                (HomotopyGroup.Pi 1
                  (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases
      threeSphere_twoPointComplement_fullChart_endpointData_loopCollapse_package
        hab basepoint target loop with
    ⟨puncture, chart, pathData, endpointData, canonicalPath, hAvoid,
      hNonempty, hPathConnected, hConnected, hSimplyConnected, hPathData,
      hEndpointData, hCanonicalSource, hCanonicalTarget, hJoined, hComponent,
      hCanonicalUnique, hQuotientSubsingleton, hLoopSource, hLoopTarget,
      hLoopHomotopic, hLoopFromPath, hPiOne⟩
  exact
    ⟨puncture, chart, pathData, endpointData, hAvoid, hNonempty,
      hPathConnected, hConnected, hSimplyConnected,
      hPathData.trans hEndpointData.symm,
      by simpa [hEndpointData] using hCanonicalSource,
      by simpa [hEndpointData] using hCanonicalTarget, hJoined, hComponent,
      by
        intro η
        simpa [hEndpointData] using hCanonicalUnique η,
      hQuotientSubsingleton, hLoopSource, hLoopTarget, hLoopHomotopic,
      hLoopFromPath, hPiOne⟩

/-- Theorem contract for
`threeSphere_twoPointComplement_fullChart_endpointData_direct_loopCollapse_package`. -/
theorem threeSphere_twoPointComplement_fullChart_endpointData_direct_loopCollapse_package_eq :
    @Poincare.threeSphere_twoPointComplement_fullChart_endpointData_direct_loopCollapse_package =
      @Poincare.threeSphere_twoPointComplement_fullChart_endpointData_direct_loopCollapse_package :=
  rfl

/--
The standard `ThreeSphere` two-puncture full-chart endpoint-data package
projects to the homotopy core used by transport consumers: the selected
endpoint path, its path-data coherence, homotopy uniqueness, path-quotient
collapse, loop collapse, and `π₁` subsingleton evidence.
-/
theorem threeSphere_twoPointComplement_endpointData_loopCollapse_core
    {a b : ThreeSphere} (hab : b ≠ a)
    (basepoint target : (({a} ∪ {b})ᶜ : Set ThreeSphere))
    (loop : Path basepoint basepoint) :
    ∃ pathData :
        PointedPathComponentPathData
          (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint,
      ∃ endpointData :
          PointedChosenPathEndpointData
            (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint target,
        pathData.path_to target = endpointData.path ∧
          endpointData.path 0 = basepoint ∧
          endpointData.path 1 = target ∧
          Joined basepoint target ∧
          pathComponent basepoint = Set.univ ∧
          (∀ η : Path basepoint target,
            Path.Homotopic endpointData.path η) ∧
          Subsingleton (Path.Homotopic.Quotient basepoint target) ∧
          loop 0 = basepoint ∧
          loop 1 = basepoint ∧
          Path.Homotopic loop (Path.refl basepoint) ∧
          FundamentalGroup.fromPath
              (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
            FundamentalGroup.fromPath
              (⟦Path.refl basepoint⟧ :
                Path.Homotopic.Quotient basepoint basepoint) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({a} ∪ {b})ᶜ : Set ThreeSphere) basepoint) := by
  rcases
      threeSphere_twoPointComplement_fullChart_endpointData_direct_loopCollapse_package
        hab basepoint target loop with
    ⟨_puncture, _chart, pathData, endpointData, _hAvoid, _hNonempty,
      _hPathConnected, _hConnected, _hSimplyConnected, hPathData,
      hEndpointSource, hEndpointTarget, hJoined, hComponent,
      hEndpointUnique, hQuotientSubsingleton, hLoopSource, hLoopTarget,
      hLoopHomotopic, hLoopFromPath, hPiOne⟩
  exact
    ⟨pathData, endpointData, hPathData, hEndpointSource, hEndpointTarget,
      hJoined, hComponent, hEndpointUnique, hQuotientSubsingleton,
      hLoopSource, hLoopTarget, hLoopHomotopic, hLoopFromPath, hPiOne⟩

/-- Theorem contract for `threeSphere_twoPointComplement_endpointData_loopCollapse_core`. -/
theorem threeSphere_twoPointComplement_endpointData_loopCollapse_core_eq :
    @Poincare.threeSphere_twoPointComplement_endpointData_loopCollapse_core =
      @Poincare.threeSphere_twoPointComplement_endpointData_loopCollapse_core :=
  rfl

end Poincare
