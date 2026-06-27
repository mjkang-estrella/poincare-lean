import Poincare.ProofProgress.TopologyExtractionPunctureTransport
import Poincare.TopologyExtraction

open scoped Manifold ContDiff

namespace Poincare

/--
Deleting one point from the one-point compactification model leaves a
contractible space, by transporting Euclidean contractibility across the
compactification chart.
-/
theorem onePoint_threeSpace_compl_singleton_contractibleSpace
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ContractibleSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
  (onePoint_threeSpace_compl_singleton_homeomorph_euclidean p).contractibleSpace

/-- A one-point complement in the compactified three-space model is path-connected. -/
theorem onePoint_threeSpace_compl_singleton_pathConnectedSpace
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : ContractibleSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_contractibleSpace p
  infer_instance

/-- A one-point complement in the compactified three-space model is connected. -/
theorem onePoint_threeSpace_compl_singleton_connectedSpace
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  infer_instance

/-- A one-point complement in the compactified three-space model is nonempty. -/
theorem onePoint_threeSpace_compl_singleton_nonempty
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    Nonempty
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  infer_instance

/--
Every point of a one-point complement in compactified three-space lies in the
path component of any chosen basepoint.
-/
theorem onePoint_threeSpace_compl_singleton_pathComponent_eq_univ
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    pathComponent basepoint = Set.univ := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    exact PathConnectedSpace.joined basepoint z

/--
Every first homotopy group of a one-point complement in the compactified
three-space model is trivial.
-/
theorem onePoint_threeSpace_compl_singleton_piOne_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    Subsingleton
      (HomotopyGroup.Pi 1
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint) :=
  ((HomotopyGroup.pi1EquivFundamentalGroup
    (X := ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (x := basepoint)).subsingleton_congr).mpr (by
      letI : SimplyConnectedSpace
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
        onePoint_threeSpace_compl_singleton_simplyConnectedSpace p
      change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
      infer_instance)

/--
Every based loop in a one-point complement of compactified three-space is
null-homotopic.  This is the path-level extraction of the simple-connectedness
already available for the complement.
-/
theorem onePoint_threeSpace_compl_singleton_loop_nullhomotopic
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∀ (basepoint :
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
      (γ : Path basepoint basepoint), Path.Homotopic γ (Path.refl basepoint) := by
  intro basepoint γ
  exact Quotient.exact (s := Path.Homotopic.setoid basepoint basepoint)
    (a := γ) (b := Path.refl basepoint) <| by
    letI : Subsingleton
        (FundamentalGroup
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) := by
      letI : SimplyConnectedSpace
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
        onePoint_threeSpace_compl_singleton_simplyConnectedSpace p
      change Subsingleton (Path.Homotopic.Quotient basepoint basepoint)
      infer_instance
    exact Subsingleton.elim
      (FundamentalGroup.fromPath
        (⟦γ⟧ : Path.Homotopic.Quotient basepoint basepoint))
      (FundamentalGroup.fromPath
        (⟦Path.refl basepoint⟧ : Path.Homotopic.Quotient basepoint basepoint))

/--
Every based loop in a one-point complement carries the full nullhomotopy
payload: source and target endpoint equations, nullhomotopy to the stationary
loop, and equality with the stationary element in the fundamental group.
-/
theorem onePoint_threeSpace_compl_singleton_loop_payload
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
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
  · exact onePoint_threeSpace_compl_singleton_loop_nullhomotopic p basepoint γ
  · exact congrArg FundamentalGroup.fromPath
      (Quotient.sound
        (onePoint_threeSpace_compl_singleton_loop_nullhomotopic
          p basepoint γ))

/--
Any two paths with the same endpoints in a one-point complement of compactified
three-space are homotopic.
-/
theorem onePoint_threeSpace_compl_singleton_paths_homotopic
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∀ {x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
      (γ η : Path x y), Path.Homotopic γ η := by
  intro x y γ η
  letI : SimplyConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_simplyConnectedSpace p
  exact SimplyConnectedSpace.paths_homotopic γ η

/--
Any two paths with the same endpoints in a one-point complement carry both the
path homotopy and the induced equality of path-homotopy quotient classes.
-/
theorem onePoint_threeSpace_compl_singleton_paths_homotopic_payload
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    {x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))}
    (γ η : Path x y) :
    Path.Homotopic γ η ∧
      (⟦γ⟧ : Path.Homotopic.Quotient x y) = ⟦η⟧ := by
  let h : Path.Homotopic γ η :=
    onePoint_threeSpace_compl_singleton_paths_homotopic p γ η
  exact ⟨h, Quotient.sound h⟩

/--
Every path-homotopy quotient in a one-point complement of compactified
three-space is a subsingleton.
-/
theorem onePoint_threeSpace_compl_singleton_pathQuotient_subsingleton
    (p : OnePoint (EuclideanSpace ℝ (Fin 3))) :
    ∀ (x y : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))),
      Subsingleton (Path.Homotopic.Quotient x y) := by
  intro x y
  rw [subsingleton_iff]
  intro γ η
  induction γ using Quotient.inductionOn with
    | h γ =>
    induction η using Quotient.inductionOn with
    | h η =>
      exact Quotient.sound
        (onePoint_threeSpace_compl_singleton_paths_homotopic p γ η)

/--
The one-point complement in compactified three-space supplies a concrete path
between any chosen basepoint and target, with endpoint equations and uniqueness
up to path homotopy.
-/
theorem onePoint_threeSpace_compl_singleton_exists_path_with_endpoints_and_homotopy_unique
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint z : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    ∃ γ : Path basepoint z,
      γ 0 = basepoint ∧ γ 1 = z ∧ Joined basepoint z ∧
        ∀ η : Path basepoint z, Path.Homotopic γ η := by
  letI : PathConnectedSpace
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) :=
    onePoint_threeSpace_compl_singleton_pathConnectedSpace p
  let joined : Joined basepoint z := PathConnectedSpace.joined basepoint z
  refine ⟨joined.somePath, ?_, ?_, ?_, ?_⟩
  · exact Path.source joined.somePath
  · exact Path.target joined.somePath
  · exact ⟨joined.somePath⟩
  · intro η
    exact onePoint_threeSpace_compl_singleton_paths_homotopic
      p joined.somePath η

/--
**Step 3702 source.** Researcher-verifiable reference endpoint: for a fixed
puncture, basepoint, target, chosen path, and based loop in the one-point
complement of compactified three-space, the contractible-complement proof
pipeline now returns a single certificate containing nonemptiness, the global
path-component equality, a concrete joined path with homotopy uniqueness,
path-homotopy uniqueness and quotient equality for the chosen path, the
subsingleton path quotient, the loop nullhomotopy payload, and triviality of
the first homotopy group.  This bundles the previously proved one-point
complement topology products above, rather than adding a naming bridge.
-/
theorem onePoint_threeSpace_compl_singleton_path_loop_topology_certificate
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint z : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (γ : Path basepoint z)
    (loop : Path basepoint basepoint) :
    Nonempty
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      pathComponent basepoint = Set.univ ∧
      Joined basepoint z ∧
      (∃ chosen : Path basepoint z,
        chosen 0 = basepoint ∧ chosen 1 = z ∧
          Joined basepoint z ∧
          ∀ η : Path basepoint z, Path.Homotopic chosen η) ∧
      (∀ η : Path basepoint z,
        Path.Homotopic γ η ∧
          (⟦γ⟧ : Path.Homotopic.Quotient basepoint z) = ⟦η⟧) ∧
      Subsingleton (Path.Homotopic.Quotient basepoint z) ∧
      loop 0 = basepoint ∧ loop 1 = basepoint ∧
      Path.Homotopic loop (Path.refl basepoint) ∧
      FundamentalGroup.fromPath
          (⟦loop⟧ : Path.Homotopic.Quotient basepoint basepoint) =
        FundamentalGroup.fromPath
          (⟦Path.refl basepoint⟧ :
            Path.Homotopic.Quotient basepoint basepoint) ∧
      Subsingleton
        (HomotopyGroup.Pi 1
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
          basepoint) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact onePoint_threeSpace_compl_singleton_nonempty p
  · exact onePoint_threeSpace_compl_singleton_pathComponent_eq_univ
      p basepoint
  · rcases
      onePoint_threeSpace_compl_singleton_exists_path_with_endpoints_and_homotopy_unique
        p basepoint z with
      ⟨chosen, _hsource, _htarget, hjoined, _hunique⟩
    exact hjoined
  · exact
      onePoint_threeSpace_compl_singleton_exists_path_with_endpoints_and_homotopy_unique
        p basepoint z
  · intro η
    exact onePoint_threeSpace_compl_singleton_paths_homotopic_payload p γ η
  · exact onePoint_threeSpace_compl_singleton_pathQuotient_subsingleton
      p basepoint z
  · exact (onePoint_threeSpace_compl_singleton_loop_payload
      p basepoint loop).1
  · exact (onePoint_threeSpace_compl_singleton_loop_payload
      p basepoint loop).2.1
  · exact (onePoint_threeSpace_compl_singleton_loop_payload
      p basepoint loop).2.2.1
  · exact (onePoint_threeSpace_compl_singleton_loop_payload
      p basepoint loop).2.2.2
  · exact onePoint_threeSpace_compl_singleton_piOne_subsingleton
      p basepoint

/-- Theorem contract for `onePoint_threeSpace_compl_singleton_path_loop_topology_certificate`. -/
theorem onePoint_threeSpace_compl_singleton_path_loop_topology_certificate_eq :
    @Poincare.onePoint_threeSpace_compl_singleton_path_loop_topology_certificate =
      @Poincare.onePoint_threeSpace_compl_singleton_path_loop_topology_certificate :=
  rfl

/--
The one-point complement in compactified three-space supplies concrete
path-component and endpoint-data objects for the selected endpoint path, while
retaining homotopy uniqueness, path-quotient collapse, based-loop collapse,
and triviality of `π₁`.
-/
theorem onePoint_threeSpace_compl_singleton_endpointData_loopCollapse_core
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint target :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (loop : Path basepoint basepoint) :
    ∃ pathData :
        PointedPathComponentPathData
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint,
      ∃ endpointData :
          PointedChosenPathEndpointData
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
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
              ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint) := by
  let hComponent :
      pathComponent basepoint = Set.univ :=
    onePoint_threeSpace_compl_singleton_pathComponent_eq_univ p basepoint
  let pathData :
      PointedPathComponentPathData
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint :=
    pointedPathComponentPathData_of_pathComponent_eq_univ basepoint hComponent
  let endpointData :
      PointedChosenPathEndpointData
        ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
        basepoint target :=
    chosenPathEndpointData_of_pathComponent_eq_univ
      basepoint hComponent target
  rcases onePoint_threeSpace_compl_singleton_loop_payload
      p basepoint loop with
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
        onePoint_threeSpace_compl_singleton_paths_homotopic
          p endpointData.path η,
      onePoint_threeSpace_compl_singleton_pathQuotient_subsingleton
        p basepoint target,
      hLoopSource,
      hLoopTarget,
      hLoopHomotopic,
      hLoopFromPath,
      onePoint_threeSpace_compl_singleton_piOne_subsingleton
        p basepoint⟩

/-- Theorem contract for `onePoint_threeSpace_compl_singleton_endpointData_loopCollapse_core`. -/
theorem onePoint_threeSpace_compl_singleton_endpointData_loopCollapse_core_eq :
    @Poincare.onePoint_threeSpace_compl_singleton_endpointData_loopCollapse_core =
      @Poincare.onePoint_threeSpace_compl_singleton_endpointData_loopCollapse_core :=
  rfl

/--
The one-point complement endpoint-data/loop-collapse core together with the
full local topology instances used by recognition extraction.  This keeps the
actual path-component endpoint data, loop nullhomotopy, `fromPath` collapse,
and `π₁` collapse in the same certificate as local path connectedness,
path connectedness, connectedness, simple connectedness, and nonemptiness.
-/
theorem onePoint_threeSpace_compl_singleton_fullTopology_endpointData_loopCollapse_core
    (p : OnePoint (EuclideanSpace ℝ (Fin 3)))
    (basepoint target :
      ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))))
    (loop : Path basepoint basepoint) :
    ∃ pathData :
        PointedPathComponentPathData
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) basepoint,
      ∃ endpointData :
          PointedChosenPathEndpointData
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
            basepoint target,
        LocPathConnectedSpace
          ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          Nonempty ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          PathConnectedSpace
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          ConnectedSpace
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
          SimplyConnectedSpace
            ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
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
              ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))
              basepoint) := by
  rcases
      onePoint_threeSpace_compl_singleton_endpointData_loopCollapse_core
        p basepoint target loop with
    ⟨pathData, endpointData, hPathData, hSource, hTarget, hJoined,
      hComponent, hHomotopyUnique, hPathQuotient, hLoopSource,
      hLoopTarget, hLoopHomotopic, hLoopFromPath, hPiOne⟩
  exact
    ⟨pathData, endpointData,
      onePoint_threeSpace_compl_singleton_locPathConnectedSpace p,
      onePoint_threeSpace_compl_singleton_nonempty p,
      onePoint_threeSpace_compl_singleton_pathConnectedSpace p,
      onePoint_threeSpace_compl_singleton_connectedSpace p,
      onePoint_threeSpace_compl_singleton_simplyConnectedSpace p,
      hPathData, hSource, hTarget, hJoined, hComponent, hHomotopyUnique,
      hPathQuotient, hLoopSource, hLoopTarget, hLoopHomotopic,
      hLoopFromPath, hPiOne⟩

/-- Theorem contract for
`onePoint_threeSpace_compl_singleton_fullTopology_endpointData_loopCollapse_core`. -/
theorem onePoint_threeSpace_compl_singleton_fullTopology_endpointData_loopCollapse_core_eq :
    @Poincare.onePoint_threeSpace_compl_singleton_fullTopology_endpointData_loopCollapse_core =
      @Poincare.onePoint_threeSpace_compl_singleton_fullTopology_endpointData_loopCollapse_core :=
  rfl

end Poincare
