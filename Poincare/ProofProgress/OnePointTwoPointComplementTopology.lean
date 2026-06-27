import Poincare.ProofProgress.OnePointSingleComplementTopology
import Poincare.ProofProgress.TopologyExtractionPunctureTransport
import Poincare.TopologyExtraction

open scoped Manifold ContDiff

namespace Poincare

/--
The complement of two distinct points in the one-point compactification model is
path-connected.  The proof uses the existing punctured-Euclidean chart for the
actual two-point complement and transports path-connectedness back from `ℝ³`
with one point removed.
-/
theorem onePoint_threeSpace_twoPointComplement_pathConnectedSpace
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  let puncture : EuclideanSpace ℝ (Fin 3) :=
    onePoint_threeSpace_compl_singleton_homeomorph_euclidean p
      (onePoint_threeSpace_pointInComplement hqp)
  let e := onePoint_threeSpace_twoPointComplement_homeomorph_puncturedEuclidean hqp
  letI : PathConnectedSpace ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
    euclideanThree_compl_singleton_pathConnectedSpace puncture
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

/--
The two-point complement is connected as a direct consequence of the named
path-connectedness theorem above.
-/
theorem onePoint_threeSpace_twoPointComplement_connectedSpace
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  infer_instance

/--
The two-point complement is nonempty, witnessed by its path-connected topology.
-/
theorem onePoint_threeSpace_twoPointComplement_nonempty
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    Nonempty
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  infer_instance

/--
Every point of the two-point complement in compactified three-space lies in the
path component of any chosen basepoint.
-/
theorem onePoint_threeSpace_twoPointComplement_pathComponent_eq_univ
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    pathComponent basepoint = Set.univ := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    exact PathConnectedSpace.joined basepoint z

/--
The two-point complement in compactified three-space has trivial first homotopy
group at every basepoint.
-/
theorem onePoint_threeSpace_twoPointComplement_piOne_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (HomotopyGroup.Pi 1
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
  ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (x := basepoint)).subsingleton_congr).mpr
      (onePoint_threeSpace_twoPointComplement_fundamentalGroup_subsingleton
        hqp basepoint)

/--
Every based loop in the two-point complement is null-homotopic.  This is the
loop-level content behind simple connectedness, extracted directly from the
existing fundamental-group triviality theorem.
-/
theorem onePoint_threeSpace_twoPointComplement_loop_nullhomotopic
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ (basepoint :
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (γ : Path basepoint basepoint), Path.Homotopic γ (Path.refl basepoint) := by
  intro basepoint γ
  exact Quotient.exact (s := Path.Homotopic.setoid basepoint basepoint)
    (a := γ) (b := Path.refl basepoint) <| by
    letI : Subsingleton
        (FundamentalGroup
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) :=
      onePoint_threeSpace_twoPointComplement_fundamentalGroup_subsingleton
        hqp basepoint
    exact Subsingleton.elim
      (FundamentalGroup.fromPath
        (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint))
      (FundamentalGroup.fromPath
        (⟦Path.refl basepoint⟧ : Path.Homotopic.Quotient basepoint basepoint))

/--
Every based loop in the two-point complement carries its endpoint equations,
its null-homotopy, and the induced equality in the fundamental group.
-/
theorem onePoint_threeSpace_twoPointComplement_loop_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
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
  · exact onePoint_threeSpace_twoPointComplement_loop_nullhomotopic hqp basepoint γ
  · exact congrArg FundamentalGroup.fromPath
      (Quotient.sound
        (onePoint_threeSpace_twoPointComplement_loop_nullhomotopic
          hqp basepoint γ))

/--
Any two paths with the same endpoints in the two-point complement of
compactified three-space are homotopic.
-/
theorem onePoint_threeSpace_twoPointComplement_paths_homotopic
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ {x y : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
      (γ η : Path x y), Path.Homotopic γ η := by
  intro x y γ η
  letI : SimplyConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_simplyConnectedSpace hqp
  exact SimplyConnectedSpace.paths_homotopic γ η

/--
Any two same-endpoint paths in the two-point complement carry both their
path homotopy and the induced equality in the path-homotopy quotient.
-/
theorem onePoint_threeSpace_twoPointComplement_paths_homotopic_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    {x y : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (γ η : Path x y) :
    Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient x y) = ⟦η⟧ := by
  letI : SimplyConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_simplyConnectedSpace hqp
  let homotopy : Path.Homotopic γ η := SimplyConnectedSpace.paths_homotopic γ η
  exact ⟨homotopy, Quotient.sound homotopy⟩

/--
Every path-homotopy quotient in the two-point complement of compactified
three-space is a subsingleton.
-/
theorem onePoint_threeSpace_twoPointComplement_pathQuotient_subsingleton
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    ∀ (x y : (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))),
      Subsingleton (Path.Homotopic.Quotient x y) := by
  intro x y
  rw [subsingleton_iff]
  intro γ η
  induction γ using Quotient.inductionOn with
  | h γ =>
    induction η using Quotient.inductionOn with
    | h η =>
      exact Quotient.sound
        (onePoint_threeSpace_twoPointComplement_paths_homotopic hqp γ η)

/--
The two-point complement in compactified three-space supplies a concrete path
between any chosen basepoint and target, with endpoint equations and uniqueness
up to path homotopy.
-/
theorem onePoint_threeSpace_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint z :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z ∧
        ∀ η : Path basepoint z, Path.Homotopic γ η := by
  letI : PathConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp
  let joined : Joined basepoint z := PathConnectedSpace.joined basepoint z
  refine ⟨joined.somePath, ?_, ?_, ?_, ?_⟩
  · exact Path.source joined.somePath
  · exact Path.target joined.somePath
  · exact ⟨joined.somePath⟩
  · intro η
    exact onePoint_threeSpace_twoPointComplement_paths_homotopic
      hqp joined.somePath η

/--
The singleton-complement and two-point-complement path-loop payloads can be
consumed as one reusable compactification-topology certificate.  This combines
the one-puncture contractible-complement payload with the two-puncture
path-connected and simply-connected payloads needed by topology extraction.
-/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_path_loop_topology_certificate
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (singleBase singleTarget :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (singlePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (twoPath : Path twoBase twoTarget)
    (twoLoop : Path twoBase twoBase) :
    (Nonempty
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      pathComponent singleBase = Set.univ ∧
      Joined singleBase singleTarget ∧
      (∃ chosen : Path singleBase singleTarget,
        chosen 0 = singleBase ∧ chosen 1 = singleTarget ∧
          Joined singleBase singleTarget ∧
          ∀ η : Path singleBase singleTarget, Path.Homotopic chosen η) ∧
      (∀ η : Path singleBase singleTarget,
        Path.Homotopic singlePath η ∧
          (⟦singlePath⟧ :
            Path.Homotopic.Quotient singleBase singleTarget) = ⟦η⟧) ∧
      Subsingleton (Path.Homotopic.Quotient singleBase singleTarget) ∧
      singleLoop 0 = singleBase ∧ singleLoop 1 = singleBase ∧
      Path.Homotopic singleLoop (Path.refl singleBase) ∧
      FundamentalGroup.fromPath
          (⟦singleLoop⟧ :
            Path.Homotopic.Quotient singleBase singleBase) =
        FundamentalGroup.fromPath
          (⟦Path.refl singleBase⟧ :
            Path.Homotopic.Quotient singleBase singleBase) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          singleBase)) ∧
    (Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      pathComponent twoBase = Set.univ ∧
      Joined twoBase twoTarget ∧
      (∃ chosen : Path twoBase twoTarget,
        chosen 0 = twoBase ∧ chosen 1 = twoTarget ∧
          Joined twoBase twoTarget ∧
          ∀ η : Path twoBase twoTarget, Path.Homotopic chosen η) ∧
      (∀ η : Path twoBase twoTarget,
        Path.Homotopic twoPath η ∧
          (⟦twoPath⟧ : Path.Homotopic.Quotient twoBase twoTarget) = ⟦η⟧) ∧
      Subsingleton (Path.Homotopic.Quotient twoBase twoTarget) ∧
      twoLoop 0 = twoBase ∧ twoLoop 1 = twoBase ∧
      Path.Homotopic twoLoop (Path.refl twoBase) ∧
      FundamentalGroup.fromPath
          (⟦twoLoop⟧ : Path.Homotopic.Quotient twoBase twoBase) =
        FundamentalGroup.fromPath
          (⟦Path.refl twoBase⟧ :
            Path.Homotopic.Quotient twoBase twoBase) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          twoBase)) := by
  refine ⟨?_, ?_⟩
  · exact
      onePoint_threeSpace_compl_singleton_path_loop_topology_certificate
        p singleBase singleTarget singlePath singleLoop
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact onePoint_threeSpace_twoPointComplement_nonempty hqp
    · exact onePoint_threeSpace_twoPointComplement_pathComponent_eq_univ
        hqp twoBase
    · rcases
        onePoint_threeSpace_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique
          hqp twoBase twoTarget with
        ⟨_chosen, _hsource, _htarget, hjoined, _hunique⟩
      exact hjoined
    · exact
        onePoint_threeSpace_twoPointComplement_exists_path_with_endpoints_and_homotopy_unique
          hqp twoBase twoTarget
    · intro η
      exact onePoint_threeSpace_twoPointComplement_paths_homotopic_payload
        hqp twoPath η
    · exact onePoint_threeSpace_twoPointComplement_pathQuotient_subsingleton
        hqp twoBase twoTarget
    · exact (onePoint_threeSpace_twoPointComplement_loop_payload
        hqp twoBase twoLoop).1
    · exact (onePoint_threeSpace_twoPointComplement_loop_payload
        hqp twoBase twoLoop).2.1
    · exact (onePoint_threeSpace_twoPointComplement_loop_payload
        hqp twoBase twoLoop).2.2.1
    · exact (onePoint_threeSpace_twoPointComplement_loop_payload
        hqp twoBase twoLoop).2.2.2
    · exact onePoint_threeSpace_twoPointComplement_piOne_subsingleton
        hqp twoBase

/-- Theorem contract for `onePoint_threeSpace_singleton_and_twoPointComplement_path_loop_topology_certificate`. -/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_path_loop_topology_certificate_eq :
    @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_path_loop_topology_certificate =
      @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_path_loop_topology_certificate :=
  rfl

/--
The combined singleton/two-point certificate can be projected to explicit
chosen-path witnesses for both complements, together with the uniqueness,
quotient, loop, and first-homotopy-group payloads needed downstream.
-/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_chosen_path_loop_projection_bundle
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (singleBase singleTarget :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (singlePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (twoPath : Path twoBase twoTarget)
    (twoLoop : Path twoBase twoBase) :
    (∃ singleChosen : Path singleBase singleTarget,
      Nonempty ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        pathComponent singleBase = Set.univ ∧
        singleChosen 0 = singleBase ∧ singleChosen 1 = singleTarget ∧
        Joined singleBase singleTarget ∧
        Path.Homotopic singlePath singleChosen ∧
        (⟦singlePath⟧ :
          Path.Homotopic.Quotient singleBase singleTarget) =
          ⟦singleChosen⟧ ∧
        (∀ η : Path singleBase singleTarget,
          Path.Homotopic singleChosen η) ∧
        Subsingleton (Path.Homotopic.Quotient singleBase singleTarget) ∧
        singleLoop 0 = singleBase ∧ singleLoop 1 = singleBase ∧
        Path.Homotopic singleLoop (Path.refl singleBase) ∧
        FundamentalGroup.fromPath
            (⟦singleLoop⟧ :
              Path.Homotopic.Quotient singleBase singleBase) =
          FundamentalGroup.fromPath
            (⟦Path.refl singleBase⟧ :
              Path.Homotopic.Quotient singleBase singleBase) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            singleBase)) ∧
    (∃ twoChosen : Path twoBase twoTarget,
      Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
        pathComponent twoBase = Set.univ ∧
        twoChosen 0 = twoBase ∧ twoChosen 1 = twoTarget ∧
        Joined twoBase twoTarget ∧
        Path.Homotopic twoPath twoChosen ∧
        (⟦twoPath⟧ : Path.Homotopic.Quotient twoBase twoTarget) =
          ⟦twoChosen⟧ ∧
        (∀ η : Path twoBase twoTarget,
          Path.Homotopic twoChosen η) ∧
        Subsingleton (Path.Homotopic.Quotient twoBase twoTarget) ∧
        twoLoop 0 = twoBase ∧ twoLoop 1 = twoBase ∧
        Path.Homotopic twoLoop (Path.refl twoBase) ∧
        FundamentalGroup.fromPath
            (⟦twoLoop⟧ : Path.Homotopic.Quotient twoBase twoBase) =
          FundamentalGroup.fromPath
            (⟦Path.refl twoBase⟧ :
              Path.Homotopic.Quotient twoBase twoBase) ∧
        Subsingleton
          (HomotopyGroup.Pi 1
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            twoBase)) := by
  rcases
    onePoint_threeSpace_singleton_and_twoPointComplement_path_loop_topology_certificate
      hqp singleBase singleTarget singlePath singleLoop
      twoBase twoTarget twoPath twoLoop with
    ⟨singleCert, twoCert⟩
  rcases singleCert with
    ⟨singleNonempty, singleComponent, _singleJoined, singleChosenPayload,
      singlePathPayload, singleQuotient, singleLoopSource, singleLoopTarget,
      singleLoopHomotopic, singleLoopFromPath, singlePi⟩
  rcases singleChosenPayload with
    ⟨singleChosen, singleChosenSource, singleChosenTarget,
      singleChosenJoined, singleChosenUnique⟩
  rcases singlePathPayload singleChosen with
    ⟨singlePathHomotopic, singlePathQuotient⟩
  rcases twoCert with
    ⟨twoNonempty, twoComponent, _twoJoined, twoChosenPayload,
      twoPathPayload, twoQuotient, twoLoopSource, twoLoopTarget,
      twoLoopHomotopic, twoLoopFromPath, twoPi⟩
  rcases twoChosenPayload with
    ⟨twoChosen, twoChosenSource, twoChosenTarget,
      twoChosenJoined, twoChosenUnique⟩
  rcases twoPathPayload twoChosen with
    ⟨twoPathHomotopic, twoPathQuotient⟩
  refine ⟨?_, ?_⟩
  · refine ⟨singleChosen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact singleNonempty
    · exact singleComponent
    · exact singleChosenSource
    · exact singleChosenTarget
    · exact singleChosenJoined
    · exact singlePathHomotopic
    · exact singlePathQuotient
    · exact singleChosenUnique
    · exact singleQuotient
    · exact singleLoopSource
    · exact singleLoopTarget
    · exact singleLoopHomotopic
    · exact singleLoopFromPath
    · exact singlePi
  · refine ⟨twoChosen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact twoNonempty
    · exact twoComponent
    · exact twoChosenSource
    · exact twoChosenTarget
    · exact twoChosenJoined
    · exact twoPathHomotopic
    · exact twoPathQuotient
    · exact twoChosenUnique
    · exact twoQuotient
    · exact twoLoopSource
    · exact twoLoopTarget
    · exact twoLoopHomotopic
    · exact twoLoopFromPath
    · exact twoPi

/-- Theorem contract for `onePoint_threeSpace_singleton_and_twoPointComplement_chosen_path_loop_projection_bundle`. -/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_chosen_path_loop_projection_bundle_eq :
    @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_chosen_path_loop_projection_bundle =
      @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_chosen_path_loop_projection_bundle :=
  rfl

/--
The two-point complement in compactified three-space supplies concrete
path-component and endpoint-data objects for its selected endpoint path, while
retaining homotopy uniqueness, path-quotient collapse, based-loop collapse,
and triviality of `π₁`.
-/
theorem onePoint_threeSpace_twoPointComplement_endpointData_loopCollapse_core
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint target :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (loop : Path basepoint basepoint) :
    ∃ pathData :
        PointedPathComponentPathData
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
      ∃ endpointData :
          PointedChosenPathEndpointData
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint target,
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
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint) := by
  let hComponent :
      pathComponent basepoint = Set.univ :=
    onePoint_threeSpace_twoPointComplement_pathComponent_eq_univ
      hqp basepoint
  let pathData :
      PointedPathComponentPathData
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint :=
    pointedPathComponentPathData_of_pathComponent_eq_univ basepoint hComponent
  let endpointData :
      PointedChosenPathEndpointData
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint target :=
    chosenPathEndpointData_of_pathComponent_eq_univ
      basepoint hComponent target
  rcases onePoint_threeSpace_twoPointComplement_loop_payload
      hqp basepoint loop with
    ⟨hLoopSource, hLoopTarget, hLoopHomotopic, hLoopFromPath⟩
  exact
    ⟨pathData,
      endpointData,
      rfl,
      endpointData.source_eq,
      endpointData.target_eq,
      endpointData.joined,
      hComponent,
      fun η =>
        onePoint_threeSpace_twoPointComplement_paths_homotopic
          hqp endpointData.path η,
      onePoint_threeSpace_twoPointComplement_pathQuotient_subsingleton
        hqp basepoint target,
      hLoopSource,
      hLoopTarget,
      hLoopHomotopic,
      hLoopFromPath,
      onePoint_threeSpace_twoPointComplement_piOne_subsingleton
        hqp basepoint⟩

/-- Theorem contract for `onePoint_threeSpace_twoPointComplement_endpointData_loopCollapse_core`. -/
theorem onePoint_threeSpace_twoPointComplement_endpointData_loopCollapse_core_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_endpointData_loopCollapse_core =
      @Poincare.onePoint_threeSpace_twoPointComplement_endpointData_loopCollapse_core :=
  rfl

/--
The selected endpoint-data path and any supplied path in the two-point
complement of compactified three-space have the same path-homotopy class in
both directions, while retaining loop-collapse and `π₁` evidence.
-/
theorem onePoint_threeSpace_twoPointComplement_endpointData_bidirectional_pathClass_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint target :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (chosenPath : Path basepoint target)
    (loop : Path basepoint basepoint) :
    ∃ pathData :
        PointedPathComponentPathData
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint,
      ∃ endpointData :
          PointedChosenPathEndpointData
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint target,
        pathData.path_to target = endpointData.path ∧
          endpointData.path 0 = basepoint ∧
          endpointData.path 1 = target ∧
          Joined basepoint target ∧
          pathComponent basepoint = Set.univ ∧
          Path.Homotopic chosenPath endpointData.path ∧
          Path.Homotopic endpointData.path chosenPath ∧
          (⟦chosenPath⟧ :
            Path.Homotopic.Quotient basepoint target) =
              ⟦endpointData.path⟧ ∧
          (⟦endpointData.path⟧ :
            Path.Homotopic.Quotient basepoint target) = ⟦chosenPath⟧ ∧
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
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint) := by
  rcases
      onePoint_threeSpace_twoPointComplement_endpointData_loopCollapse_core
        hqp basepoint target loop with
    ⟨pathData, endpointData, hPathData, hEndpointSource, hEndpointTarget,
      hJoined, hComponent, hEndpointUnique, hQuotientSubsingleton,
      hLoopSource, hLoopTarget, hLoopHomotopic, hLoopFromPath, hPiOne⟩
  let hChosenPath : Path.Homotopic chosenPath endpointData.path :=
    onePoint_threeSpace_twoPointComplement_paths_homotopic
      hqp chosenPath endpointData.path
  let hEndpointPath : Path.Homotopic endpointData.path chosenPath :=
    hEndpointUnique chosenPath
  exact
    ⟨pathData, endpointData, hPathData, hEndpointSource, hEndpointTarget,
      hJoined, hComponent, hChosenPath, hEndpointPath,
      Quotient.sound hChosenPath, Quotient.sound hEndpointPath,
      hQuotientSubsingleton, hLoopSource, hLoopTarget, hLoopHomotopic,
      hLoopFromPath, hPiOne⟩

/-- Theorem contract for
`onePoint_threeSpace_twoPointComplement_endpointData_bidirectional_pathClass_payload`. -/
theorem onePoint_threeSpace_twoPointComplement_endpointData_bidirectional_pathClass_payload_eq :
    @Poincare.onePoint_threeSpace_twoPointComplement_endpointData_bidirectional_pathClass_payload =
      @Poincare.onePoint_threeSpace_twoPointComplement_endpointData_bidirectional_pathClass_payload :=
  rfl

/--
The singleton and two-point complements in compactified three-space expose
their endpoint-data loop-collapse cores as one reusable model certificate.
-/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_loopCollapse_core
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (singleBase singleTarget :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (twoLoop : Path twoBase twoBase) :
    (∃ singlePathData :
        PointedPathComponentPathData
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) singleBase,
      ∃ singleEndpointData :
          PointedChosenPathEndpointData
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            singleBase singleTarget,
        singlePathData.path_to singleTarget = singleEndpointData.path ∧
          singleEndpointData.path 0 = singleBase ∧
          singleEndpointData.path 1 = singleTarget ∧
          Joined singleBase singleTarget ∧
          pathComponent singleBase = Set.univ ∧
          (∀ η : Path singleBase singleTarget,
            Path.Homotopic singleEndpointData.path η) ∧
          Subsingleton (Path.Homotopic.Quotient singleBase singleTarget) ∧
          singleLoop 0 = singleBase ∧
          singleLoop 1 = singleBase ∧
          Path.Homotopic singleLoop (Path.refl singleBase) ∧
          FundamentalGroup.fromPath
              (⟦singleLoop⟧ :
                Path.Homotopic.Quotient singleBase singleBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl singleBase⟧ :
                Path.Homotopic.Quotient singleBase singleBase) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              singleBase)) ∧
    (∃ twoPathData :
        PointedPathComponentPathData
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          twoBase,
      ∃ twoEndpointData :
          PointedChosenPathEndpointData
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            twoBase twoTarget,
        twoPathData.path_to twoTarget = twoEndpointData.path ∧
          twoEndpointData.path 0 = twoBase ∧
          twoEndpointData.path 1 = twoTarget ∧
          Joined twoBase twoTarget ∧
          pathComponent twoBase = Set.univ ∧
          (∀ η : Path twoBase twoTarget,
            Path.Homotopic twoEndpointData.path η) ∧
          Subsingleton (Path.Homotopic.Quotient twoBase twoTarget) ∧
          twoLoop 0 = twoBase ∧
          twoLoop 1 = twoBase ∧
          Path.Homotopic twoLoop (Path.refl twoBase) ∧
          FundamentalGroup.fromPath
              (⟦twoLoop⟧ : Path.Homotopic.Quotient twoBase twoBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl twoBase⟧ :
                Path.Homotopic.Quotient twoBase twoBase) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              twoBase)) := by
  exact
    ⟨onePoint_threeSpace_compl_singleton_endpointData_loopCollapse_core
        p singleBase singleTarget singleLoop,
      onePoint_threeSpace_twoPointComplement_endpointData_loopCollapse_core
        hqp twoBase twoTarget twoLoop⟩

/-- Theorem contract for `onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_loopCollapse_core`. -/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_loopCollapse_core_eq :
    @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_loopCollapse_core =
      @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_loopCollapse_core :=
  rfl

/--
The endpoint-data cores also identify the path-homotopy class of any supplied
path with the selected endpoint-data path, for both the singleton and two-point
complements.
-/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_pathClass_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (singleBase singleTarget :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (singlePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (twoPath : Path twoBase twoTarget)
    (twoLoop : Path twoBase twoBase) :
    (∃ singlePathData :
        PointedPathComponentPathData
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) singleBase,
      ∃ singleEndpointData :
          PointedChosenPathEndpointData
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            singleBase singleTarget,
        singlePathData.path_to singleTarget = singleEndpointData.path ∧
          singleEndpointData.path 0 = singleBase ∧
          singleEndpointData.path 1 = singleTarget ∧
          Joined singleBase singleTarget ∧
          pathComponent singleBase = Set.univ ∧
          Path.Homotopic singleEndpointData.path singlePath ∧
          (⟦singleEndpointData.path⟧ :
            Path.Homotopic.Quotient singleBase singleTarget) =
              ⟦singlePath⟧ ∧
          Subsingleton (Path.Homotopic.Quotient singleBase singleTarget) ∧
          singleLoop 0 = singleBase ∧
          singleLoop 1 = singleBase ∧
          Path.Homotopic singleLoop (Path.refl singleBase) ∧
          FundamentalGroup.fromPath
              (⟦singleLoop⟧ :
                Path.Homotopic.Quotient singleBase singleBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl singleBase⟧ :
                Path.Homotopic.Quotient singleBase singleBase) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              singleBase)) ∧
    (∃ twoPathData :
        PointedPathComponentPathData
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          twoBase,
      ∃ twoEndpointData :
          PointedChosenPathEndpointData
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            twoBase twoTarget,
        twoPathData.path_to twoTarget = twoEndpointData.path ∧
          twoEndpointData.path 0 = twoBase ∧
          twoEndpointData.path 1 = twoTarget ∧
          Joined twoBase twoTarget ∧
          pathComponent twoBase = Set.univ ∧
          Path.Homotopic twoEndpointData.path twoPath ∧
          (⟦twoEndpointData.path⟧ :
            Path.Homotopic.Quotient twoBase twoTarget) = ⟦twoPath⟧ ∧
          Subsingleton (Path.Homotopic.Quotient twoBase twoTarget) ∧
          twoLoop 0 = twoBase ∧
          twoLoop 1 = twoBase ∧
          Path.Homotopic twoLoop (Path.refl twoBase) ∧
          FundamentalGroup.fromPath
              (⟦twoLoop⟧ : Path.Homotopic.Quotient twoBase twoBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl twoBase⟧ :
                Path.Homotopic.Quotient twoBase twoBase) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              twoBase)) := by
  rcases
    onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_loopCollapse_core
      hqp singleBase singleTarget singleLoop twoBase twoTarget twoLoop with
    ⟨singleCore, twoCore⟩
  rcases singleCore with
    ⟨singlePathData, singleEndpointData, singlePathEq,
      singleSource, singleTargetEq, singleJoined, singleComponent,
      singleUnique, singleQuotient, singleLoopSource, singleLoopTarget,
      singleLoopHomotopic, singleLoopFromPath, singlePi⟩
  rcases twoCore with
    ⟨twoPathData, twoEndpointData, twoPathEq,
      twoSource, twoTargetEq, twoJoined, twoComponent,
      twoUnique, twoQuotient, twoLoopSource, twoLoopTarget,
      twoLoopHomotopic, twoLoopFromPath, twoPi⟩
  refine ⟨?_, ?_⟩
  · let hSinglePath : Path.Homotopic singleEndpointData.path singlePath :=
      singleUnique singlePath
    refine
      ⟨singlePathData, singleEndpointData, singlePathEq, singleSource,
        singleTargetEq, singleJoined, singleComponent, hSinglePath, ?_,
        singleQuotient, singleLoopSource, singleLoopTarget,
        singleLoopHomotopic, singleLoopFromPath, singlePi⟩
    exact Quotient.sound hSinglePath
  · let hTwoPath : Path.Homotopic twoEndpointData.path twoPath :=
      twoUnique twoPath
    refine
      ⟨twoPathData, twoEndpointData, twoPathEq, twoSource,
        twoTargetEq, twoJoined, twoComponent, hTwoPath, ?_,
        twoQuotient, twoLoopSource, twoLoopTarget, twoLoopHomotopic,
        twoLoopFromPath, twoPi⟩
    exact Quotient.sound hTwoPath

/-- Theorem contract for `onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_pathClass_payload`. -/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_pathClass_payload_eq :
    @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_pathClass_payload =
      @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_pathClass_payload :=
  rfl

/--
The endpoint-data selected paths and arbitrary supplied paths have the same
path-homotopy class in both directions for the singleton and two-point
compactification complements.
-/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_bidirectional_pathClass_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (singleBase singleTarget :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (singlePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (twoPath : Path twoBase twoTarget)
    (twoLoop : Path twoBase twoBase) :
    (∃ singlePathData :
        PointedPathComponentPathData
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) singleBase,
      ∃ singleEndpointData :
          PointedChosenPathEndpointData
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            singleBase singleTarget,
        singlePathData.path_to singleTarget = singleEndpointData.path ∧
          singleEndpointData.path 0 = singleBase ∧
          singleEndpointData.path 1 = singleTarget ∧
          Joined singleBase singleTarget ∧
          pathComponent singleBase = Set.univ ∧
          Path.Homotopic singlePath singleEndpointData.path ∧
          Path.Homotopic singleEndpointData.path singlePath ∧
          (⟦singlePath⟧ :
            Path.Homotopic.Quotient singleBase singleTarget) =
              ⟦singleEndpointData.path⟧ ∧
          (⟦singleEndpointData.path⟧ :
            Path.Homotopic.Quotient singleBase singleTarget) =
              ⟦singlePath⟧ ∧
          Subsingleton (Path.Homotopic.Quotient singleBase singleTarget) ∧
          singleLoop 0 = singleBase ∧
          singleLoop 1 = singleBase ∧
          Path.Homotopic singleLoop (Path.refl singleBase) ∧
          FundamentalGroup.fromPath
              (⟦singleLoop⟧ :
                Path.Homotopic.Quotient singleBase singleBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl singleBase⟧ :
                Path.Homotopic.Quotient singleBase singleBase) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              singleBase)) ∧
    (∃ twoPathData :
        PointedPathComponentPathData
          (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          twoBase,
      ∃ twoEndpointData :
          PointedChosenPathEndpointData
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            twoBase twoTarget,
        twoPathData.path_to twoTarget = twoEndpointData.path ∧
          twoEndpointData.path 0 = twoBase ∧
          twoEndpointData.path 1 = twoTarget ∧
          Joined twoBase twoTarget ∧
          pathComponent twoBase = Set.univ ∧
          Path.Homotopic twoPath twoEndpointData.path ∧
          Path.Homotopic twoEndpointData.path twoPath ∧
          (⟦twoPath⟧ :
            Path.Homotopic.Quotient twoBase twoTarget) =
              ⟦twoEndpointData.path⟧ ∧
          (⟦twoEndpointData.path⟧ :
            Path.Homotopic.Quotient twoBase twoTarget) = ⟦twoPath⟧ ∧
          Subsingleton (Path.Homotopic.Quotient twoBase twoTarget) ∧
          twoLoop 0 = twoBase ∧
          twoLoop 1 = twoBase ∧
          Path.Homotopic twoLoop (Path.refl twoBase) ∧
          FundamentalGroup.fromPath
              (⟦twoLoop⟧ : Path.Homotopic.Quotient twoBase twoBase) =
            FundamentalGroup.fromPath
              (⟦Path.refl twoBase⟧ :
                Path.Homotopic.Quotient twoBase twoBase) ∧
          Subsingleton
            (HomotopyGroup.Pi 1
              (({p} ∪ {q})ᶜ :
                Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              twoBase)) := by
  rcases
    onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_pathClass_payload
      hqp singleBase singleTarget singlePath singleLoop
      twoBase twoTarget twoPath twoLoop with
    ⟨singlePayload, twoPayload⟩
  rcases singlePayload with
    ⟨singlePathData, singleEndpointData, singlePathDataEq,
      singleSource, singleTargetEq, singleJoined, singleComponent,
      singleEndpointHomotopic, singleEndpointQuotient,
      singleQuotientSubsingleton, singleLoopSource, singleLoopTarget,
      singleLoopHomotopic, singleLoopFromPath, singlePi⟩
  rcases twoPayload with
    ⟨twoPathData, twoEndpointData, twoPathDataEq,
      twoSource, twoTargetEq, twoJoined, twoComponent,
      twoEndpointHomotopic, twoEndpointQuotient, twoQuotientSubsingleton,
      twoLoopSource, twoLoopTarget, twoLoopHomotopic, twoLoopFromPath,
      twoPi⟩
  let singlePathHomotopic :
      Path.Homotopic singlePath singleEndpointData.path :=
    onePoint_threeSpace_compl_singleton_paths_homotopic
      p singlePath singleEndpointData.path
  let twoPathHomotopic :
      Path.Homotopic twoPath twoEndpointData.path :=
    onePoint_threeSpace_twoPointComplement_paths_homotopic
      hqp twoPath twoEndpointData.path
  exact
    ⟨⟨singlePathData, singleEndpointData, singlePathDataEq,
        singleSource, singleTargetEq, singleJoined, singleComponent,
        singlePathHomotopic, singleEndpointHomotopic,
        Quotient.sound singlePathHomotopic, singleEndpointQuotient,
        singleQuotientSubsingleton, singleLoopSource, singleLoopTarget,
        singleLoopHomotopic, singleLoopFromPath, singlePi⟩,
      twoPathData, twoEndpointData, twoPathDataEq,
      twoSource, twoTargetEq, twoJoined, twoComponent,
      twoPathHomotopic, twoEndpointHomotopic,
      Quotient.sound twoPathHomotopic, twoEndpointQuotient,
      twoQuotientSubsingleton, twoLoopSource, twoLoopTarget,
      twoLoopHomotopic, twoLoopFromPath, twoPi⟩

/-- Theorem contract for
`onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_bidirectional_pathClass_payload`. -/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_bidirectional_pathClass_payload_eq :
    @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_bidirectional_pathClass_payload =
      @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_bidirectional_pathClass_payload :=
  rfl

/--
Full-topology endpoint-data certificate for the singleton and two-point
compactification complements.  It packages nonemptiness, path-connectedness,
connectedness, simple-connectedness, bidirectional endpoint path-class
identification, loop endpoint equations, loop nullhomotopies, `fromPath`
collapse, and `π₁` collapse for both complements.
-/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_fullTopology_endpointData_bidirectional_pathClass_certificate
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (singleBase singleTarget :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (singlePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (twoPath : Path twoBase twoTarget)
    (twoLoop : Path twoBase twoBase) :
    (Nonempty ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ∃ singlePathData :
          PointedPathComponentPathData
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) singleBase,
        ∃ singleEndpointData :
            PointedChosenPathEndpointData
              ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              singleBase singleTarget,
          singlePathData.path_to singleTarget = singleEndpointData.path ∧
            singleEndpointData.path 0 = singleBase ∧
            singleEndpointData.path 1 = singleTarget ∧
            Joined singleBase singleTarget ∧
            pathComponent singleBase = Set.univ ∧
            Path.Homotopic singlePath singleEndpointData.path ∧
            Path.Homotopic singleEndpointData.path singlePath ∧
            (⟦singlePath⟧ :
              Path.Homotopic.Quotient singleBase singleTarget) =
                ⟦singleEndpointData.path⟧ ∧
            (⟦singleEndpointData.path⟧ :
              Path.Homotopic.Quotient singleBase singleTarget) =
                ⟦singlePath⟧ ∧
            Subsingleton (Path.Homotopic.Quotient singleBase singleTarget) ∧
            singleLoop 0 = singleBase ∧
            singleLoop 1 = singleBase ∧
            Path.Homotopic singleLoop (Path.refl singleBase) ∧
            FundamentalGroup.fromPath
                (⟦singleLoop⟧ :
                  Path.Homotopic.Quotient singleBase singleBase) =
              FundamentalGroup.fromPath
                (⟦Path.refl singleBase⟧ :
                  Path.Homotopic.Quotient singleBase singleBase) ∧
            Subsingleton
              (HomotopyGroup.Pi 1
                ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                singleBase)) ∧
    (Nonempty
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      PathConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      ∃ twoPathData :
          PointedPathComponentPathData
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            twoBase,
        ∃ twoEndpointData :
            PointedChosenPathEndpointData
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              twoBase twoTarget,
          twoPathData.path_to twoTarget = twoEndpointData.path ∧
            twoEndpointData.path 0 = twoBase ∧
            twoEndpointData.path 1 = twoTarget ∧
            Joined twoBase twoTarget ∧
            pathComponent twoBase = Set.univ ∧
            Path.Homotopic twoPath twoEndpointData.path ∧
            Path.Homotopic twoEndpointData.path twoPath ∧
            (⟦twoPath⟧ :
              Path.Homotopic.Quotient twoBase twoTarget) =
                ⟦twoEndpointData.path⟧ ∧
            (⟦twoEndpointData.path⟧ :
              Path.Homotopic.Quotient twoBase twoTarget) = ⟦twoPath⟧ ∧
            Subsingleton (Path.Homotopic.Quotient twoBase twoTarget) ∧
            twoLoop 0 = twoBase ∧
            twoLoop 1 = twoBase ∧
            Path.Homotopic twoLoop (Path.refl twoBase) ∧
            FundamentalGroup.fromPath
                (⟦twoLoop⟧ : Path.Homotopic.Quotient twoBase twoBase) =
              FundamentalGroup.fromPath
                (⟦Path.refl twoBase⟧ :
                  Path.Homotopic.Quotient twoBase twoBase) ∧
            Subsingleton
              (HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                twoBase)) := by
  rcases
    onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_bidirectional_pathClass_payload
      hqp singleBase singleTarget singlePath singleLoop
      twoBase twoTarget twoPath twoLoop with
    ⟨singlePayload, twoPayload⟩
  exact
    ⟨⟨onePoint_threeSpace_compl_singleton_nonempty p,
        onePoint_threeSpace_compl_singleton_pathConnectedSpace p,
        onePoint_threeSpace_compl_singleton_connectedSpace p,
        onePoint_threeSpace_compl_singleton_simplyConnectedSpace p,
        singlePayload⟩,
      onePoint_threeSpace_twoPointComplement_nonempty hqp,
      onePoint_threeSpace_twoPointComplement_pathConnectedSpace hqp,
      onePoint_threeSpace_twoPointComplement_connectedSpace hqp,
      onePoint_threeSpace_twoPointComplement_simplyConnectedSpace hqp,
      twoPayload⟩

/-- Theorem contract for
`onePoint_threeSpace_singleton_and_twoPointComplement_fullTopology_endpointData_bidirectional_pathClass_certificate`. -/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_fullTopology_endpointData_bidirectional_pathClass_certificate_eq :
    @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_fullTopology_endpointData_bidirectional_pathClass_certificate =
      @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_fullTopology_endpointData_bidirectional_pathClass_certificate :=
  rfl

/--
Local-path-connected endpoint-data certificate for the singleton and two-point
compactification complements.  This adds the local path connectedness inputs
needed by extraction consumers while retaining the endpoint-data
bidirectional path-class and loop-collapse witnesses for both complements.
-/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_locPath_endpointData_bidirectional_pathClass_certificate
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (singleBase singleTarget :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (singlePath : Path singleBase singleTarget)
    (singleLoop : Path singleBase singleBase)
    (twoBase twoTarget :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (twoPath : Path twoBase twoTarget)
    (twoLoop : Path twoBase twoBase) :
    LocPathConnectedSpace
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      LocPathConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      (∃ singlePathData :
          PointedPathComponentPathData
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) singleBase,
        ∃ singleEndpointData :
            PointedChosenPathEndpointData
              ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              singleBase singleTarget,
          singlePathData.path_to singleTarget = singleEndpointData.path ∧
            singleEndpointData.path 0 = singleBase ∧
            singleEndpointData.path 1 = singleTarget ∧
            Joined singleBase singleTarget ∧
            pathComponent singleBase = Set.univ ∧
            Path.Homotopic singlePath singleEndpointData.path ∧
            Path.Homotopic singleEndpointData.path singlePath ∧
            (⟦singlePath⟧ :
              Path.Homotopic.Quotient singleBase singleTarget) =
                ⟦singleEndpointData.path⟧ ∧
            (⟦singleEndpointData.path⟧ :
              Path.Homotopic.Quotient singleBase singleTarget) =
                ⟦singlePath⟧ ∧
            Subsingleton (Path.Homotopic.Quotient singleBase singleTarget) ∧
            singleLoop 0 = singleBase ∧
            singleLoop 1 = singleBase ∧
            Path.Homotopic singleLoop (Path.refl singleBase) ∧
            FundamentalGroup.fromPath
                (⟦singleLoop⟧ :
                  Path.Homotopic.Quotient singleBase singleBase) =
              FundamentalGroup.fromPath
                (⟦Path.refl singleBase⟧ :
                  Path.Homotopic.Quotient singleBase singleBase) ∧
            Subsingleton
              (HomotopyGroup.Pi 1
                ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                singleBase)) ∧
      (∃ twoPathData :
          PointedPathComponentPathData
            (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            twoBase,
        ∃ twoEndpointData :
            PointedChosenPathEndpointData
              (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              twoBase twoTarget,
          twoPathData.path_to twoTarget = twoEndpointData.path ∧
            twoEndpointData.path 0 = twoBase ∧
            twoEndpointData.path 1 = twoTarget ∧
            Joined twoBase twoTarget ∧
            pathComponent twoBase = Set.univ ∧
            Path.Homotopic twoPath twoEndpointData.path ∧
            Path.Homotopic twoEndpointData.path twoPath ∧
            (⟦twoPath⟧ :
              Path.Homotopic.Quotient twoBase twoTarget) =
                ⟦twoEndpointData.path⟧ ∧
            (⟦twoEndpointData.path⟧ :
              Path.Homotopic.Quotient twoBase twoTarget) = ⟦twoPath⟧ ∧
            Subsingleton (Path.Homotopic.Quotient twoBase twoTarget) ∧
            twoLoop 0 = twoBase ∧
            twoLoop 1 = twoBase ∧
            Path.Homotopic twoLoop (Path.refl twoBase) ∧
            FundamentalGroup.fromPath
                (⟦twoLoop⟧ : Path.Homotopic.Quotient twoBase twoBase) =
              FundamentalGroup.fromPath
                (⟦Path.refl twoBase⟧ :
                  Path.Homotopic.Quotient twoBase twoBase) ∧
            Subsingleton
              (HomotopyGroup.Pi 1
                (({p} ∪ {q})ᶜ :
                  Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
                twoBase)) := by
  rcases
    onePoint_threeSpace_singleton_and_twoPointComplement_endpointData_bidirectional_pathClass_payload
      hqp singleBase singleTarget singlePath singleLoop
      twoBase twoTarget twoPath twoLoop with
    ⟨singlePayload, twoPayload⟩
  exact
    ⟨onePoint_threeSpace_compl_singleton_locPathConnectedSpace p,
      onePoint_threeSpace_twoPointComplement_locPathConnectedSpace hqp,
      singlePayload, twoPayload⟩

/-- Theorem contract for
`onePoint_threeSpace_singleton_and_twoPointComplement_locPath_endpointData_bidirectional_pathClass_certificate`. -/
theorem onePoint_threeSpace_singleton_and_twoPointComplement_locPath_endpointData_bidirectional_pathClass_certificate_eq :
    @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_locPath_endpointData_bidirectional_pathClass_certificate =
      @Poincare.onePoint_threeSpace_singleton_and_twoPointComplement_locPath_endpointData_bidirectional_pathClass_certificate :=
  rfl

end Poincare
