/-
Small proof-bearing assembly lemmas around the statement layer.

These lemmas do not prove the Poincare Conjecture. They record safe consequences
that can be used once future proof-bearing dependency theorems exist.
-/

import Poincare.Statement

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
A diffeomorphism to the standard 3-sphere gives a homeomorphism to the standard
3-sphere.

This is a real Lean theorem using mathlib's `Diffeomorph.toHomeomorph`, but it
is only an assembly lemma. It does not construct the required diffeomorphism.
-/
theorem homeomorph_of_diffeomorph_three_sphere
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) →
      Nonempty (M ≃ₜ ThreeSphere) := by
  rintro ⟨h⟩
  exact ⟨h.toHomeomorph⟩

/--
A diffeomorphism from the standard 3-sphere to `M` also gives a homeomorphism
from `M` back to the standard 3-sphere.
-/
theorem homeomorph_of_threeSphere_diffeomorph
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) →
      Nonempty (M ≃ₜ ThreeSphere) := by
  rintro ⟨h⟩
  exact ⟨h.symm.toHomeomorph⟩

/--
Invert a diffeomorphism from `M` to the standard 3-sphere.
-/
theorem threeSphere_diffeomorph_of_diffeomorph_to_threeSphere
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) →
      Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) := by
  rintro ⟨h⟩
  exact ⟨h.symm⟩

/--
Invert a diffeomorphism from the standard 3-sphere to `M`.
-/
theorem diffeomorph_to_threeSphere_of_threeSphere_diffeomorph
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) →
      Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  rintro ⟨h⟩
  exact ⟨h.symm⟩

/--
Being diffeomorphic to the standard 3-sphere is independent of which side of
the diffeomorphism the standard sphere is written on.
-/
theorem diffeomorph_to_threeSphere_iff_threeSphere_diffeomorph
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) ↔
      Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) := by
  constructor
  · exact threeSphere_diffeomorph_of_diffeomorph_to_threeSphere
  · exact diffeomorph_to_threeSphere_of_threeSphere_diffeomorph

/-- The standard 3-sphere is smoothly diffeomorphic to itself. -/
theorem threeSphere_self_diffeomorph :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  exact ⟨Diffeomorph.refl (𝓡 3) ThreeSphere ∞⟩

/-- The standard 3-sphere self-diffeomorphism witness is reflexivity. -/
theorem threeSphere_self_diffeomorph_eq :
    threeSphere_self_diffeomorph =
      ⟨Diffeomorph.refl (𝓡 3) ThreeSphere ∞⟩ := by
  apply Subsingleton.elim

/--
The reflexive smooth self-diffeomorphism of the standard 3-sphere gives the
reflexive topological self-homeomorphism through the smooth-to-topological
assembly bridge.
-/
theorem threeSphere_self_homeomorph_of_self_diffeomorph :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  homeomorph_of_diffeomorph_three_sphere threeSphere_self_diffeomorph

/--
The standard sphere self-homeomorphism route is exactly the smooth
self-diffeomorphism route followed by the smooth-to-topological bridge.
-/
theorem threeSphere_self_homeomorph_of_self_diffeomorph_eq :
    threeSphere_self_homeomorph_of_self_diffeomorph =
      homeomorph_of_diffeomorph_three_sphere threeSphere_self_diffeomorph := by
  apply Subsingleton.elim

/--
The available standard-sphere target prerequisites pair with the reflexive
smooth self-diffeomorphism endpoint, with no simple-connectedness input needed.
-/
theorem threeSphere_self_diffeomorph_payload :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  exact ⟨threeSphere_target_prerequisites_except_simpleConnected,
    threeSphere_self_diffeomorph⟩

/--
The standard-sphere self-diffeomorphism payload is exactly the target
prerequisite payload paired with the reflexive smooth self-diffeomorphism.
-/
theorem threeSphere_self_diffeomorph_payload_eq :
    threeSphere_self_diffeomorph_payload =
      ⟨threeSphere_target_prerequisites_except_simpleConnected,
        threeSphere_self_diffeomorph⟩ := by
  apply Subsingleton.elim

/-- Project the target-prerequisite component from the self-diffeomorphism payload. -/
theorem threeSphere_target_prerequisites_except_simpleConnected_of_self_diffeomorph_payload :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  rcases threeSphere_self_diffeomorph_payload with ⟨prerequisites, _endpoint⟩
  exact prerequisites

/-- The projected prerequisite component is the named standard-sphere payload. -/
theorem threeSphere_target_prerequisites_except_simpleConnected_of_self_diffeomorph_payload_eq :
    threeSphere_target_prerequisites_except_simpleConnected_of_self_diffeomorph_payload =
      threeSphere_target_prerequisites_except_simpleConnected := by
  apply Subsingleton.elim

/-- Project the reflexive smooth endpoint from the self-diffeomorphism payload. -/
theorem threeSphere_self_diffeomorph_of_self_diffeomorph_payload :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  rcases threeSphere_self_diffeomorph_payload with ⟨_prerequisites, endpoint⟩
  exact endpoint

/-- The projected smooth endpoint is the named reflexive self-diffeomorphism. -/
theorem threeSphere_self_diffeomorph_of_self_diffeomorph_payload_eq :
    threeSphere_self_diffeomorph_of_self_diffeomorph_payload =
      threeSphere_self_diffeomorph := by
  apply Subsingleton.elim

/--
The same prerequisite payload pairs with the self-homeomorphism obtained from
the reflexive smooth self-diffeomorphism.
-/
theorem threeSphere_self_homeomorph_payload_of_self_diffeomorph :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  exact ⟨threeSphere_target_prerequisites_except_simpleConnected,
    threeSphere_self_homeomorph_of_self_diffeomorph⟩

/--
The smooth-forgetful self-homeomorphism payload is exactly the target
prerequisite payload paired with the named self-homeomorphism route.
-/
theorem threeSphere_self_homeomorph_payload_of_self_diffeomorph_eq :
    threeSphere_self_homeomorph_payload_of_self_diffeomorph =
      ⟨threeSphere_target_prerequisites_except_simpleConnected,
        threeSphere_self_homeomorph_of_self_diffeomorph⟩ := by
  apply Subsingleton.elim

/-- Project the target-prerequisite component from the smooth-forgetful payload. -/
theorem threeSphere_target_prerequisites_except_simpleConnected_of_self_homeomorph_payload_of_self_diffeomorph :
    ∃ _t2 : T2Space ThreeSphere,
    ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
    ∃ _compact : CompactSpace ThreeSphere,
    ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
    ∃ _path : PathConnectedSpace ThreeSphere,
    ∃ _connected : ConnectedSpace ThreeSphere,
      Nonempty ThreeSphere := by
  rcases threeSphere_self_homeomorph_payload_of_self_diffeomorph with
    ⟨prerequisites, _endpoint⟩
  exact prerequisites

/-- The projected prerequisite component is the named standard-sphere payload. -/
theorem threeSphere_target_prerequisites_except_simpleConnected_of_self_homeomorph_payload_of_self_diffeomorph_eq :
    threeSphere_target_prerequisites_except_simpleConnected_of_self_homeomorph_payload_of_self_diffeomorph =
      threeSphere_target_prerequisites_except_simpleConnected := by
  apply Subsingleton.elim

/-- Project the topological endpoint from the smooth-forgetful payload. -/
theorem threeSphere_self_homeomorph_of_self_homeomorph_payload_of_self_diffeomorph :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  rcases threeSphere_self_homeomorph_payload_of_self_diffeomorph with
    ⟨_prerequisites, endpoint⟩
  exact endpoint

/-- The projected topological endpoint is the named smooth-forgetful route. -/
theorem threeSphere_self_homeomorph_of_self_homeomorph_payload_of_self_diffeomorph_eq :
    threeSphere_self_homeomorph_of_self_homeomorph_payload_of_self_diffeomorph =
      threeSphere_self_homeomorph_of_self_diffeomorph := by
  apply Subsingleton.elim

/--
Applying the project target statement to the standard sphere itself only needs
the standard sphere's simple-connectedness as an additional local input.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement
    [SimplyConnectedSpace ThreeSphere]
    (h : PoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  exact h ThreeSphere

/--
The self-case projection from the project target is exactly application to the
standard sphere.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_self_homeomorph_of_poincare_statement =
      (fun h : PoincareConjectureStatement.{0} => h ThreeSphere) := by
  funext h
  apply Subsingleton.elim

/--
Applying the smooth target statement to the standard sphere itself gives the
standard smooth self-diffeomorphism witness, again modulo the local
simple-connectedness input.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement
    [SimplyConnectedSpace ThreeSphere]
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  exact h ThreeSphere

/--
The smooth self-case projection is exactly application of the smooth statement
to the standard sphere.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_self_diffeomorph_of_smooth_statement =
      (fun h : SmoothPoincareConjectureStatement.{0} => h ThreeSphere) := by
  funext h
  apply Subsingleton.elim

/--
The smooth target statement also gives the standard topological
self-homeomorphism after forgetting the self-diffeomorphism to a homeomorphism.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement
    [SimplyConnectedSpace ThreeSphere]
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  exact homeomorph_of_diffeomorph_three_sphere (h ThreeSphere)

/--
The smooth-to-topological self-case route is exactly smooth self-application
followed by `homeomorph_of_diffeomorph_three_sphere`.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_self_homeomorph_of_smooth_statement =
      (fun h : SmoothPoincareConjectureStatement.{0} =>
        homeomorph_of_diffeomorph_three_sphere (h ThreeSphere)) := by
  funext h
  apply Subsingleton.elim

/--
Applying the project target to the standard sphere exposes both the full
homotopy-oriented standard-sphere prerequisite payload and the self-homeomorphism
endpoint.  The simple-connectedness of `S^3` remains an explicit input.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement
    [SimplyConnectedSpace ThreeSphere]
    (h : PoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  exact ⟨threeSphere_homotopy_prerequisites,
    threeSphere_self_homeomorph_of_poincare_statement h⟩

/--
The project-target self-application payload is exactly the homotopy prerequisite
payload paired with the existing self-homeomorphism route.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_self_homeomorph_payload_of_poincare_statement =
      (fun h : PoincareConjectureStatement.{0} =>
        ⟨threeSphere_homotopy_prerequisites,
          threeSphere_self_homeomorph_of_poincare_statement h⟩) := by
  funext h
  apply Subsingleton.elim

/--
The bare project-target self payload also agrees with the explicit
direct-simple prerequisite route.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_direct_simple_route_eq
    [SimplyConnectedSpace ThreeSphere]
    (h : PoincareConjectureStatement.{0}) :
    threeSphere_self_homeomorph_payload_of_poincare_statement h =
      ⟨threeSphere_homotopy_prerequisites_of_simpleConnectedSpace,
        threeSphere_self_homeomorph_of_poincare_statement h⟩ := by
  apply Subsingleton.elim

/--
Applying the smooth target to the standard sphere exposes the same prerequisite
payload with the smooth self-diffeomorphism endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement
    [SimplyConnectedSpace ThreeSphere]
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  exact ⟨threeSphere_homotopy_prerequisites,
    threeSphere_self_diffeomorph_of_smooth_statement h⟩

/--
The smooth self-diffeomorphism payload is exactly the homotopy prerequisite
payload paired with the existing smooth self-application route.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_self_diffeomorph_payload_of_smooth_statement =
      (fun h : SmoothPoincareConjectureStatement.{0} =>
        ⟨threeSphere_homotopy_prerequisites,
          threeSphere_self_diffeomorph_of_smooth_statement h⟩) := by
  funext h
  apply Subsingleton.elim

/--
The bare smooth self-diffeomorphism payload also agrees with the explicit
direct-simple prerequisite route.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_direct_simple_route_eq
    [SimplyConnectedSpace ThreeSphere]
    (h : SmoothPoincareConjectureStatement.{0}) :
    threeSphere_self_diffeomorph_payload_of_smooth_statement h =
      ⟨threeSphere_homotopy_prerequisites_of_simpleConnectedSpace,
        threeSphere_self_diffeomorph_of_smooth_statement h⟩ := by
  apply Subsingleton.elim

/--
The smooth target also exposes the homotopy prerequisite payload with the
topological self-homeomorphism obtained by forgetting smooth structure.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement
    [SimplyConnectedSpace ThreeSphere]
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  exact ⟨threeSphere_homotopy_prerequisites,
    threeSphere_self_homeomorph_of_smooth_statement h⟩

/--
The smooth-to-topological self payload is exactly the homotopy prerequisite
payload paired with the existing smooth-to-topological self route.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_eq
    [SimplyConnectedSpace ThreeSphere] :
    threeSphere_self_homeomorph_payload_of_smooth_statement =
      (fun h : SmoothPoincareConjectureStatement.{0} =>
        ⟨threeSphere_homotopy_prerequisites,
          threeSphere_self_homeomorph_of_smooth_statement h⟩) := by
  funext h
  apply Subsingleton.elim

/--
The bare smooth-to-topological self payload also agrees with the explicit
direct-simple prerequisite route.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_direct_simple_route_eq
    [SimplyConnectedSpace ThreeSphere]
    (h : SmoothPoincareConjectureStatement.{0}) :
    threeSphere_self_homeomorph_payload_of_smooth_statement h =
      ⟨threeSphere_homotopy_prerequisites_of_simpleConnectedSpace,
        threeSphere_self_homeomorph_of_smooth_statement h⟩ := by
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation is enough to apply the project target
statement to the standard sphere itself.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement
    (hLoop : ThreeSphereLoopNullhomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
  exact threeSphere_self_homeomorph_of_poincare_statement h

/--
The target-statement self route from loop-nullhomotopy is exactly the existing
self route after converting loop-nullhomotopy to simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement =
      (fun hLoop : ThreeSphereLoopNullhomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
          threeSphere_self_homeomorph_of_poincare_statement h) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation is enough to apply the smooth target
statement to the standard sphere itself.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement
    (hLoop : ThreeSphereLoopNullhomotopyStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
  exact threeSphere_self_diffeomorph_of_smooth_statement h

/--
The smooth self-diffeomorphism route from loop-nullhomotopy is exactly the
existing smooth self route after converting loop-nullhomotopy to
simple-connectedness.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement =
      (fun hLoop : ThreeSphereLoopNullhomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
          threeSphere_self_diffeomorph_of_smooth_statement h) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The smooth target plus the concrete loop-nullhomotopy obligation gives the
topological self-homeomorphism after forgetting smooth structure.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement
    (hLoop : ThreeSphereLoopNullhomotopyStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
  exact threeSphere_self_homeomorph_of_smooth_statement h

/--
The smooth-to-topological self route from loop-nullhomotopy is exactly the
existing smooth-to-topological self route after converting loop-nullhomotopy to
simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement =
      (fun hLoop : ThreeSphereLoopNullhomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
          threeSphere_self_homeomorph_of_smooth_statement h) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The target fundamental-group obligation is enough to apply the project target
statement to the standard sphere itself.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_fundamentalGroupSubsingletonStatement
    (hFund : ThreeSphereFundamentalGroupSubsingletonStatement)
    (h : PoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement hFund
  exact threeSphere_self_homeomorph_of_poincare_statement h

/--
The target-statement self route from the fundamental-group formulation is
exactly the existing self route after converting that formulation to
simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement hFund
          threeSphere_self_homeomorph_of_poincare_statement h) := by
  funext hFund h
  apply Subsingleton.elim

/-- The fundamental-group target self route agrees with the loop route. -/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_fundamentalGroupSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
              hFund) h) := by
  funext hFund h
  apply Subsingleton.elim

/--
The target fundamental-group obligation is enough to apply the smooth target
statement to the standard sphere itself.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
    (hFund : ThreeSphereFundamentalGroupSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement hFund
  exact threeSphere_self_diffeomorph_of_smooth_statement h

/--
The smooth self-diffeomorphism route from the fundamental-group formulation is
exactly the existing smooth self route after converting that formulation to
simple-connectedness.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement hFund
          threeSphere_self_diffeomorph_of_smooth_statement h) := by
  funext hFund h
  apply Subsingleton.elim

/-- The fundamental-group smooth self-diffeomorphism route agrees with the loop route. -/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_loop_route_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
              hFund) h) := by
  funext hFund h
  apply Subsingleton.elim

/--
The smooth target plus the target fundamental-group obligation gives the
topological self-homeomorphism after forgetting smooth structure.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
    (hFund : ThreeSphereFundamentalGroupSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement hFund
  exact threeSphere_self_homeomorph_of_smooth_statement h

/--
The smooth-to-topological self route from the fundamental-group formulation is
exactly the existing smooth-to-topological self route after converting that
formulation to simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement hFund
          threeSphere_self_homeomorph_of_smooth_statement h) := by
  funext hFund h
  apply Subsingleton.elim

/-- The fundamental-group smooth-to-topological self route agrees with the loop route. -/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
              hFund) h) := by
  funext hFund h
  apply Subsingleton.elim

/--
The target `π₁` obligation is enough to apply the project target statement to
the standard sphere itself.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement
    (hPiOne : ThreeSpherePiOneSubsingletonStatement)
    (h : PoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement hPiOne
  exact threeSphere_self_homeomorph_of_poincare_statement h

/--
The target-statement self route from the `π₁` formulation is exactly the
existing self route after converting that formulation to simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement hPiOne
          threeSphere_self_homeomorph_of_poincare_statement h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` target self route agrees with the fundamental-group route. -/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement_fundamentalGroup_route_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` target self route agrees with the loop route. -/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/--
The target `π₁` obligation is enough to apply the smooth target statement to
the standard sphere itself.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement
    (hPiOne : ThreeSpherePiOneSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement hPiOne
  exact threeSphere_self_diffeomorph_of_smooth_statement h

/--
The smooth self-diffeomorphism route from the `π₁` formulation is exactly the
existing smooth self route after converting that formulation to
simple-connectedness.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement hPiOne
          threeSphere_self_diffeomorph_of_smooth_statement h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` smooth self-diffeomorphism route agrees with the fundamental-group route. -/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement_fundamentalGroup_route_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` smooth self-diffeomorphism route agrees with the loop route. -/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement_loop_route_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/--
The smooth target plus the target `π₁` obligation gives the topological
self-homeomorphism after forgetting smooth structure.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement
    (hPiOne : ThreeSpherePiOneSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement hPiOne
  exact threeSphere_self_homeomorph_of_smooth_statement h

/--
The smooth-to-topological self route from the `π₁` formulation is exactly the
existing smooth-to-topological self route after converting that formulation to
simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement hPiOne
          threeSphere_self_homeomorph_of_smooth_statement h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` smooth-to-topological self route agrees with the fundamental-group route. -/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement_fundamentalGroup_route_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` smooth-to-topological self route agrees with the loop route. -/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/--
The based loop-nullhomotopy obligation is enough to apply the project target
statement to the standard sphere itself.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint)
    (h : PoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement hBased
  exact threeSphere_self_homeomorph_of_poincare_statement h

/--
The target-statement self route from based loop-nullhomotopy is exactly the
existing self route after converting based loop-nullhomotopy to
simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement hBased
          threeSphere_self_homeomorph_of_poincare_statement h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop target-statement self route agrees with the full-loop route. -/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement_loop_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop target-statement self route agrees with the fundamental-group route. -/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement_fundamentalGroup_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop target-statement self route agrees with the `π₁` route. -/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement_piOne_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement
            (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
The based loop-nullhomotopy obligation is enough to apply the smooth target
statement to the standard sphere itself.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement hBased
  exact threeSphere_self_diffeomorph_of_smooth_statement h

/--
The smooth self-diffeomorphism route from based loop-nullhomotopy is exactly
the existing smooth self route after converting based loop-nullhomotopy to
simple-connectedness.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement hBased
          threeSphere_self_diffeomorph_of_smooth_statement h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self-diffeomorphism route agrees with the full-loop route. -/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_loop_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self-diffeomorphism route agrees with the fundamental-group route. -/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_fundamentalGroup_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self-diffeomorphism route agrees with the `π₁` route. -/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_piOne_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement
            (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
The smooth target plus the based loop-nullhomotopy obligation gives the
topological self-homeomorphism after forgetting smooth structure.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement hBased
  exact threeSphere_self_homeomorph_of_smooth_statement h

/--
The smooth-to-topological self route from based loop-nullhomotopy is exactly
the existing smooth-to-topological self route after converting based
loop-nullhomotopy to simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement hBased
          threeSphere_self_homeomorph_of_smooth_statement h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth-to-topological self route agrees with the full-loop route. -/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_loop_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth-to-topological self route agrees with the fundamental-group route. -/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_fundamentalGroup_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth-to-topological self route agrees with the `π₁` route. -/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_piOne_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement
            (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation is enough to apply the project target
statement to the standard sphere itself.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_pathHomotopyStatement
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
  exact threeSphere_self_homeomorph_of_poincare_statement h

/--
The target-statement self route from path-homotopy is exactly the existing self
route after converting path-homotopy to simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_pathHomotopyStatement_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
          threeSphere_self_homeomorph_of_poincare_statement h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The direct path-homotopy target self route agrees with the route that first
converts path-homotopy to loop-nullhomotopy.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_pathHomotopyStatement_loop_route_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation is enough to apply the smooth target
statement to the standard sphere itself.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_pathHomotopyStatement
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
  exact threeSphere_self_diffeomorph_of_smooth_statement h

/--
The smooth self-diffeomorphism route from path-homotopy is exactly the existing
smooth self route after converting path-homotopy to simple-connectedness.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_pathHomotopyStatement_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
          threeSphere_self_diffeomorph_of_smooth_statement h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The direct path-homotopy smooth self route agrees with the route that first
converts path-homotopy to loop-nullhomotopy.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_pathHomotopyStatement_loop_route_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The smooth target plus the concrete path-homotopy obligation gives the
topological self-homeomorphism after forgetting smooth structure.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_pathHomotopyStatement
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
  exact threeSphere_self_homeomorph_of_smooth_statement h

/--
The smooth-to-topological self route from path-homotopy is exactly the existing
smooth-to-topological self route after converting path-homotopy to
simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_pathHomotopyStatement_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
          threeSphere_self_homeomorph_of_smooth_statement h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The direct path-homotopy smooth-to-topological self route agrees with the route
that first converts path-homotopy to loop-nullhomotopy.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_pathHomotopyStatement_loop_route_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The concrete path-quotient uniqueness obligation is enough to apply the
project target statement to the standard sphere itself.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement
    (hQuot : ThreeSpherePathQuotientSubsingletonStatement)
    (h : PoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement hQuot
  exact threeSphere_self_homeomorph_of_poincare_statement h

/--
The target-statement self route from path-quotient uniqueness is exactly the
existing self route after converting quotient uniqueness to simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement hQuot
          threeSphere_self_homeomorph_of_poincare_statement h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient target self route agrees with the route that first
converts quotient uniqueness to path-homotopy uniqueness.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement_path_route_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient target self route also agrees with the
loop-nullhomotopy route obtained through path-homotopy uniqueness.
-/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement
              (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot)) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The concrete path-quotient uniqueness obligation is enough to apply the smooth
target statement to the standard sphere itself.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement
    (hQuot : ThreeSpherePathQuotientSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement hQuot
  exact threeSphere_self_diffeomorph_of_smooth_statement h

/--
The smooth self-diffeomorphism route from path-quotient uniqueness is exactly
the existing smooth self route after converting quotient uniqueness to
simple-connectedness.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement hQuot
          threeSphere_self_diffeomorph_of_smooth_statement h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient smooth self route agrees with the route that first
converts quotient uniqueness to path-homotopy uniqueness.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement_path_route_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient smooth self route also agrees with the
loop-nullhomotopy route obtained through path-homotopy uniqueness.
-/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement_loop_route_eq :
    threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement
              (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot)) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The smooth target plus the concrete path-quotient uniqueness obligation gives
the topological self-homeomorphism after forgetting smooth structure.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement
    (hQuot : ThreeSpherePathQuotientSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    Nonempty (ThreeSphere ≃ₜ ThreeSphere) := by
  letI : SimplyConnectedSpace ThreeSphere :=
    threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement hQuot
  exact threeSphere_self_homeomorph_of_smooth_statement h

/--
The smooth-to-topological self route from path-quotient uniqueness is exactly
the existing smooth-to-topological self route after converting quotient
uniqueness to simple-connectedness.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement hQuot
          threeSphere_self_homeomorph_of_smooth_statement h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient smooth-to-topological self route agrees with the route
that first converts quotient uniqueness to path-homotopy uniqueness.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement_path_route_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient smooth-to-topological self route also agrees with the
loop-nullhomotopy route obtained through path-homotopy uniqueness.
-/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement
              (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot)) h) := by
  funext hQuot h
  apply Subsingleton.elim

/-- The based-loop target-statement self route agrees with the path-homotopy route. -/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement_path_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop target-statement self route agrees with the path-quotient route. -/
theorem threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement_pathQuotient_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement
            (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self-diffeomorphism route agrees with the path-homotopy route. -/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_path_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self-diffeomorphism route agrees with the path-quotient route. -/
theorem threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_pathQuotient_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement
            (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth-to-topological self route agrees with the path-homotopy route. -/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_path_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth-to-topological self route agrees with the path-quotient route. -/
theorem threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement_pathQuotient_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement
            (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation exposes the target self route as a
payload carrying both the homotopy-oriented prerequisite bundle and the
self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement
    (hLoop : ThreeSphereLoopNullhomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement hLoop,
    threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement hLoop h⟩

/--
The loop-nullhomotopy target self payload is exactly the concrete prerequisite
route paired with the loop-nullhomotopy target endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement =
      (fun hLoop : ThreeSphereLoopNullhomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement hLoop,
            threeSphere_self_homeomorph_of_poincare_statement_and_loopNullhomotopyStatement
              hLoop h⟩) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The loop-nullhomotopy target self payload is the bare self payload under the
simple-connectedness instance derived from loop-nullhomotopy.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement =
      (fun hLoop : ThreeSphereLoopNullhomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
          threeSphere_self_homeomorph_payload_of_poincare_statement h) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation exposes the smooth self route as a
payload carrying both the homotopy-oriented prerequisite bundle and the
self-diffeomorphism endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
    (hLoop : ThreeSphereLoopNullhomotopyStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement hLoop,
    threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement hLoop h⟩

/--
The loop-nullhomotopy smooth self payload is exactly the concrete prerequisite
route paired with the loop-nullhomotopy smooth endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement =
      (fun hLoop : ThreeSphereLoopNullhomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement hLoop,
            threeSphere_self_diffeomorph_of_smooth_statement_and_loopNullhomotopyStatement
              hLoop h⟩) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The loop-nullhomotopy smooth self payload is the bare smooth self payload under
the simple-connectedness instance derived from loop-nullhomotopy.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement_bare_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement =
      (fun hLoop : ThreeSphereLoopNullhomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
          threeSphere_self_diffeomorph_payload_of_smooth_statement h) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The concrete loop-nullhomotopy obligation exposes the smooth-to-topological self
route as a payload carrying both the homotopy-oriented prerequisite bundle and
the self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
    (hLoop : ThreeSphereLoopNullhomotopyStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement hLoop,
    threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement hLoop h⟩

/--
The loop-nullhomotopy smooth-to-topological self payload is exactly the concrete
prerequisite route paired with the loop-nullhomotopy smooth-to-topological
endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement =
      (fun hLoop : ThreeSphereLoopNullhomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_loopNullhomotopyStatement hLoop,
            threeSphere_self_homeomorph_of_smooth_statement_and_loopNullhomotopyStatement
              hLoop h⟩) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The loop-nullhomotopy smooth-to-topological payload is the bare
smooth-to-topological payload under the simple-connectedness instance derived
from loop-nullhomotopy.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement =
      (fun hLoop : ThreeSphereLoopNullhomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_loopNullhomotopyStatement hLoop
          threeSphere_self_homeomorph_payload_of_smooth_statement h) := by
  funext hLoop h
  apply Subsingleton.elim

/--
The target fundamental-group obligation exposes the target self route as a
payload carrying both the homotopy-oriented prerequisite bundle and the
self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_fundamentalGroupSubsingletonStatement
    (hFund : ThreeSphereFundamentalGroupSubsingletonStatement)
    (h : PoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement hFund,
    threeSphere_self_homeomorph_of_poincare_statement_and_fundamentalGroupSubsingletonStatement
      hFund h⟩

/--
The fundamental-group target self payload is exactly the fundamental-group
prerequisite route paired with the fundamental-group target endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement
              hFund,
            threeSphere_self_homeomorph_of_poincare_statement_and_fundamentalGroupSubsingletonStatement
              hFund h⟩) := by
  funext hFund h
  apply Subsingleton.elim

/--
The fundamental-group target self payload is the bare self payload under the
simple-connectedness instance derived from the fundamental-group formulation.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_fundamentalGroupSubsingletonStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement hFund
          threeSphere_self_homeomorph_payload_of_poincare_statement h) := by
  funext hFund h
  apply Subsingleton.elim

/-- The fundamental-group target self payload agrees with the loop payload route. -/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_fundamentalGroupSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
              hFund) h) := by
  funext hFund h
  apply Subsingleton.elim

/--
The target fundamental-group obligation exposes the smooth self route as a
payload carrying both the homotopy-oriented prerequisite bundle and the
self-diffeomorphism endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
    (hFund : ThreeSphereFundamentalGroupSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement hFund,
    threeSphere_self_diffeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
      hFund h⟩

/--
The fundamental-group smooth self payload is exactly the fundamental-group
prerequisite route paired with the fundamental-group smooth endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement
              hFund,
            threeSphere_self_diffeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
              hFund h⟩) := by
  funext hFund h
  apply Subsingleton.elim

/--
The fundamental-group smooth self payload is the bare smooth self payload under
the simple-connectedness instance derived from the fundamental-group
formulation.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_bare_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement hFund
          threeSphere_self_diffeomorph_payload_of_smooth_statement h) := by
  funext hFund h
  apply Subsingleton.elim

/-- The fundamental-group smooth self payload agrees with the loop payload route. -/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_loop_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
              hFund) h) := by
  funext hFund h
  apply Subsingleton.elim

/--
The target fundamental-group obligation exposes the smooth-to-topological self
route as a payload carrying both the homotopy-oriented prerequisite bundle and
the self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
    (hFund : ThreeSphereFundamentalGroupSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement hFund,
    threeSphere_self_homeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
      hFund h⟩

/--
The fundamental-group smooth-to-topological self payload is exactly the
fundamental-group prerequisite route paired with the fundamental-group
smooth-to-topological endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_fundamentalGroupSubsingletonStatement
              hFund,
            threeSphere_self_homeomorph_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
              hFund h⟩) := by
  funext hFund h
  apply Subsingleton.elim

/--
The fundamental-group smooth-to-topological payload is the bare
smooth-to-topological payload under the simple-connectedness instance derived
from the fundamental-group formulation.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_fundamentalGroupSubsingletonStatement hFund
          threeSphere_self_homeomorph_payload_of_smooth_statement h) := by
  funext hFund h
  apply Subsingleton.elim

/-- The fundamental-group smooth-to-topological self payload agrees with the loop payload route. -/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement =
      (fun hFund : ThreeSphereFundamentalGroupSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_fundamentalGroupSubsingletonStatement
              hFund) h) := by
  funext hFund h
  apply Subsingleton.elim

/--
The target `π₁` obligation exposes the target self route as a payload carrying
both the homotopy-oriented prerequisite bundle and the self-homeomorphism
endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement
    (hPiOne : ThreeSpherePiOneSubsingletonStatement)
    (h : PoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement hPiOne,
    threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement
      hPiOne h⟩

/--
The `π₁` target self payload is exactly the `π₁` prerequisite route paired with
the `π₁` target endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement hPiOne,
            threeSphere_self_homeomorph_of_poincare_statement_and_piOneSubsingletonStatement
              hPiOne h⟩) := by
  funext hPiOne h
  apply Subsingleton.elim

/--
The `π₁` target self payload is the bare self payload under the
simple-connectedness instance derived from the `π₁` formulation.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement hPiOne
          threeSphere_self_homeomorph_payload_of_poincare_statement h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` target self payload agrees with the fundamental-group payload route. -/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement_fundamentalGroup_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` target self payload agrees with the loop payload route. -/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/--
The target `π₁` obligation exposes the smooth self route as a payload carrying
both the homotopy-oriented prerequisite bundle and the self-diffeomorphism
endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement
    (hPiOne : ThreeSpherePiOneSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement hPiOne,
    threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement
      hPiOne h⟩

/--
The `π₁` smooth self payload is exactly the `π₁` prerequisite route paired with
the `π₁` smooth endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement hPiOne,
            threeSphere_self_diffeomorph_of_smooth_statement_and_piOneSubsingletonStatement
              hPiOne h⟩) := by
  funext hPiOne h
  apply Subsingleton.elim

/--
The `π₁` smooth self payload is the bare smooth self payload under the
simple-connectedness instance derived from the `π₁` formulation.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement_bare_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement hPiOne
          threeSphere_self_diffeomorph_payload_of_smooth_statement h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` smooth self payload agrees with the fundamental-group payload route. -/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement_fundamentalGroup_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` smooth self payload agrees with the loop payload route. -/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement_loop_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/--
The target `π₁` obligation exposes the smooth-to-topological self route as a
payload carrying both the homotopy-oriented prerequisite bundle and the
self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement
    (hPiOne : ThreeSpherePiOneSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement hPiOne,
    threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement
      hPiOne h⟩

/--
The `π₁` smooth-to-topological self payload is exactly the `π₁` prerequisite
route paired with the `π₁` smooth-to-topological endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_piOneSubsingletonStatement hPiOne,
            threeSphere_self_homeomorph_of_smooth_statement_and_piOneSubsingletonStatement
              hPiOne h⟩) := by
  funext hPiOne h
  apply Subsingleton.elim

/--
The `π₁` smooth-to-topological payload is the bare smooth-to-topological
payload under the simple-connectedness instance derived from the `π₁`
formulation.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_piOneSubsingletonStatement hPiOne
          threeSphere_self_homeomorph_payload_of_smooth_statement h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` smooth-to-topological self payload agrees with the fundamental-group payload route. -/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement_fundamentalGroup_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/-- The `π₁` smooth-to-topological self payload agrees with the loop payload route. -/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement =
      (fun hPiOne : ThreeSpherePiOneSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_piOneSubsingletonStatement
              hPiOne) h) := by
  funext hPiOne h
  apply Subsingleton.elim

/--
The based loop-nullhomotopy obligation exposes the target self route as a
payload carrying both the homotopy-oriented prerequisite bundle and the
self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint)
    (h : PoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement hBased,
    threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement
      hBased h⟩

/--
The based-loop target self payload is exactly the based-loop prerequisite route
paired with the based-loop target endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement hBased,
            threeSphere_self_homeomorph_of_poincare_statement_and_basedLoopNullhomotopyStatement
              hBased h⟩) := by
  funext hBased h
  apply Subsingleton.elim

/--
The based-loop target self payload is the bare self payload under the
simple-connectedness instance derived from the based-loop formulation.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement_bare_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement hBased
          threeSphere_self_homeomorph_payload_of_poincare_statement h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop target self payload agrees with the full-loop payload route. -/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement_loop_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop target self payload agrees with the fundamental-group payload route. -/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement_fundamentalGroup_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop target self payload agrees with the `π₁` payload route. -/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement_piOne_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_piOneSubsingletonStatement
            (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
The based loop-nullhomotopy obligation exposes the smooth self route as a
payload carrying both the homotopy-oriented prerequisite bundle and the
self-diffeomorphism endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement hBased,
    threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
      hBased h⟩

/--
The based-loop smooth self payload is exactly the based-loop prerequisite route
paired with the based-loop smooth endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement hBased,
            threeSphere_self_diffeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
              hBased h⟩) := by
  funext hBased h
  apply Subsingleton.elim

/--
The based-loop smooth self payload is the bare smooth self payload under the
simple-connectedness instance derived from the based-loop formulation.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_bare_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement hBased
          threeSphere_self_diffeomorph_payload_of_smooth_statement h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self payload agrees with the full-loop payload route. -/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_loop_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self payload agrees with the fundamental-group payload route. -/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_fundamentalGroup_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self payload agrees with the `π₁` payload route. -/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_piOne_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement
            (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
The based loop-nullhomotopy obligation exposes the smooth-to-topological self
route as a payload carrying both the homotopy-oriented prerequisite bundle and
the self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
    {basepoint : ThreeSphere}
    (hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement hBased,
    threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
      hBased h⟩

/--
The based-loop smooth-to-topological self payload is exactly the based-loop
prerequisite route paired with the based-loop smooth-to-topological endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_basedLoopNullhomotopyStatement hBased,
            threeSphere_self_homeomorph_of_smooth_statement_and_basedLoopNullhomotopyStatement
              hBased h⟩) := by
  funext hBased h
  apply Subsingleton.elim

/--
The based-loop smooth-to-topological payload is the bare
smooth-to-topological payload under the simple-connectedness instance derived
from the based-loop formulation.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_bare_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_basedLoopNullhomotopyStatement hBased
          threeSphere_self_homeomorph_payload_of_smooth_statement h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth-to-topological self payload agrees with the full-loop payload route. -/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_loop_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth-to-topological self payload agrees with the fundamental-group payload route. -/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_fundamentalGroup_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_fundamentalGroupSubsingletonStatement
            (threeSphere_fundamentalGroupSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth-to-topological self payload agrees with the `π₁` payload route. -/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_piOne_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_piOneSubsingletonStatement
            (threeSphere_piOneSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation exposes the target self route as a
payload carrying both the homotopy-oriented prerequisite bundle and the
self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathHomotopyStatement
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : PoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_pathHomotopyStatement hPath,
    threeSphere_self_homeomorph_of_poincare_statement_and_pathHomotopyStatement hPath h⟩

/--
The path-homotopy target self payload is exactly the concrete prerequisite
route paired with the path-homotopy target endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathHomotopyStatement_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_pathHomotopyStatement hPath,
            threeSphere_self_homeomorph_of_poincare_statement_and_pathHomotopyStatement
              hPath h⟩) := by
  funext hPath h
  apply Subsingleton.elim

/--
The path-homotopy target self payload is the bare self payload under the
simple-connectedness instance derived from path-homotopy.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathHomotopyStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
          threeSphere_self_homeomorph_payload_of_poincare_statement h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The direct path-homotopy target self payload agrees with the loop-nullhomotopy
payload route after converting path-homotopy to loop-nullhomotopy.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathHomotopyStatement_loop_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation exposes the smooth self route as a
payload carrying both the homotopy-oriented prerequisite bundle and the
self-diffeomorphism endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathHomotopyStatement
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_pathHomotopyStatement hPath,
    threeSphere_self_diffeomorph_of_smooth_statement_and_pathHomotopyStatement hPath h⟩

/--
The path-homotopy smooth self payload is exactly the concrete prerequisite
route paired with the path-homotopy smooth endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathHomotopyStatement_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_pathHomotopyStatement hPath,
            threeSphere_self_diffeomorph_of_smooth_statement_and_pathHomotopyStatement
              hPath h⟩) := by
  funext hPath h
  apply Subsingleton.elim

/--
The path-homotopy smooth self payload is the bare smooth self payload under the
simple-connectedness instance derived from path-homotopy.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathHomotopyStatement_bare_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
          threeSphere_self_diffeomorph_payload_of_smooth_statement h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The direct path-homotopy smooth self payload agrees with the loop-nullhomotopy
payload route after converting path-homotopy to loop-nullhomotopy.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathHomotopyStatement_loop_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The concrete path-homotopy obligation exposes the smooth-to-topological self
route as a payload carrying both the homotopy-oriented prerequisite bundle and
the self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathHomotopyStatement
    (hPath : ThreeSpherePathHomotopyStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_pathHomotopyStatement hPath,
    threeSphere_self_homeomorph_of_smooth_statement_and_pathHomotopyStatement hPath h⟩

/--
The path-homotopy smooth-to-topological self payload is exactly the concrete
prerequisite route paired with the path-homotopy smooth-to-topological endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathHomotopyStatement_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_pathHomotopyStatement hPath,
            threeSphere_self_homeomorph_of_smooth_statement_and_pathHomotopyStatement
              hPath h⟩) := by
  funext hPath h
  apply Subsingleton.elim

/--
The path-homotopy smooth-to-topological payload is the bare
smooth-to-topological payload under the simple-connectedness instance derived
from path-homotopy.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathHomotopyStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathHomotopyStatement hPath
          threeSphere_self_homeomorph_payload_of_smooth_statement h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The direct path-homotopy smooth-to-topological self payload agrees with the
loop-nullhomotopy payload route after converting path-homotopy to
loop-nullhomotopy.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathHomotopyStatement_loop_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathHomotopyStatement =
      (fun hPath : ThreeSpherePathHomotopyStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement hPath) h) := by
  funext hPath h
  apply Subsingleton.elim

/--
The concrete path-quotient uniqueness obligation exposes the target self route
as a payload carrying both the homotopy-oriented prerequisite bundle and the
self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement
    (hQuot : ThreeSpherePathQuotientSubsingletonStatement)
    (h : PoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement hQuot,
    threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement
      hQuot h⟩

/--
The path-quotient target self payload is exactly the concrete prerequisite
route paired with the path-quotient target endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement hQuot,
            threeSphere_self_homeomorph_of_poincare_statement_and_pathQuotientSubsingletonStatement
              hQuot h⟩) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The path-quotient target self payload is the bare self payload under the
simple-connectedness instance derived from path-quotient uniqueness.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement hQuot
          threeSphere_self_homeomorph_payload_of_poincare_statement h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient target self payload agrees with the path-homotopy
payload route after converting quotient uniqueness to path-homotopy uniqueness.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement_path_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient target self payload also agrees with the
loop-nullhomotopy payload obtained through path-homotopy uniqueness.
-/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement
              (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot)) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The concrete path-quotient uniqueness obligation exposes the smooth self route
as a payload carrying both the homotopy-oriented prerequisite bundle and the
self-diffeomorphism endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement
    (hQuot : ThreeSpherePathQuotientSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement hQuot,
    threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement
      hQuot h⟩

/--
The path-quotient smooth self payload is exactly the concrete prerequisite
route paired with the path-quotient smooth endpoint.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement hQuot,
            threeSphere_self_diffeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement
              hQuot h⟩) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The path-quotient smooth self payload is the bare smooth self payload under the
simple-connectedness instance derived from path-quotient uniqueness.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement_bare_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement hQuot
          threeSphere_self_diffeomorph_payload_of_smooth_statement h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient smooth self payload agrees with the path-homotopy
payload route after converting quotient uniqueness to path-homotopy uniqueness.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement_path_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient smooth self payload also agrees with the
loop-nullhomotopy payload obtained through path-homotopy uniqueness.
-/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement_loop_route_eq :
    threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement
              (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot)) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The concrete path-quotient uniqueness obligation exposes the
smooth-to-topological self route as a payload carrying both the homotopy-oriented
prerequisite bundle and the self-homeomorphism endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement
    (hQuot : ThreeSpherePathQuotientSubsingletonStatement)
    (h : SmoothPoincareConjectureStatement.{0}) :
    ∃ _prerequisites :
      (∃ _t2 : T2Space ThreeSphere,
      ∃ _charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ThreeSphere,
      ∃ _simplyConnected : SimplyConnectedSpace ThreeSphere,
      ∃ _compact : CompactSpace ThreeSphere,
      ∃ _smooth : IsManifold (𝓡 3) ∞ ThreeSphere,
      ∃ _path : PathConnectedSpace ThreeSphere,
      ∃ _locPath : LocPathConnectedSpace ThreeSphere,
      ∃ _connected : ConnectedSpace ThreeSphere,
        Nonempty ThreeSphere),
        Nonempty (ThreeSphere ≃ₜ ThreeSphere) :=
  ⟨threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement hQuot,
    threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement
      hQuot h⟩

/--
The path-quotient smooth-to-topological self payload is exactly the concrete
prerequisite route paired with the path-quotient smooth-to-topological endpoint.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          ⟨threeSphere_homotopy_prerequisites_of_pathQuotientSubsingletonStatement hQuot,
            threeSphere_self_homeomorph_of_smooth_statement_and_pathQuotientSubsingletonStatement
              hQuot h⟩) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The path-quotient smooth-to-topological payload is the bare
smooth-to-topological payload under the simple-connectedness instance derived
from path-quotient uniqueness.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement_bare_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          letI : SimplyConnectedSpace ThreeSphere :=
            threeSphere_simplyConnectedSpace_of_pathQuotientSubsingletonStatement hQuot
          threeSphere_self_homeomorph_payload_of_smooth_statement h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient smooth-to-topological self payload agrees with the
path-homotopy payload route after converting quotient uniqueness to
path-homotopy uniqueness.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement_path_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot) h) := by
  funext hQuot h
  apply Subsingleton.elim

/--
The direct path-quotient smooth-to-topological self payload also agrees with the
loop-nullhomotopy payload obtained through path-homotopy uniqueness.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement_loop_route_eq :
    threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement =
      (fun hQuot : ThreeSpherePathQuotientSubsingletonStatement =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_loopNullhomotopyStatement
            (threeSphere_loopNullhomotopyStatement_of_pathHomotopyStatement
              (threeSphere_pathHomotopyStatement_of_pathQuotientSubsingletonStatement hQuot)) h) := by
  funext hQuot h
  apply Subsingleton.elim

/-- The based-loop target self payload agrees with the path-homotopy payload route. -/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement_path_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop target self payload agrees with the path-quotient payload route. -/
theorem threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement_pathQuotient_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : PoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_poincare_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : PoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_poincare_statement_and_pathQuotientSubsingletonStatement
            (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self payload agrees with the path-homotopy payload route. -/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_path_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/-- The based-loop smooth self payload agrees with the path-quotient payload route. -/
theorem threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_pathQuotient_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_diffeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_diffeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement
            (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
The based-loop smooth-to-topological self payload agrees with the
path-homotopy payload route.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_path_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathHomotopyStatement
            (threeSphere_pathHomotopyStatement_of_basedLoopNullhomotopyStatement hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
The based-loop smooth-to-topological self payload agrees with the
path-quotient payload route.
-/
theorem threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement_pathQuotient_route_eq
    (basepoint : ThreeSphere) :
    (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
      fun h : SmoothPoincareConjectureStatement.{0} =>
        threeSphere_self_homeomorph_payload_of_smooth_statement_and_basedLoopNullhomotopyStatement
          hBased h) =
      (fun hBased : ThreeSphereBasedLoopNullhomotopyStatement basepoint =>
        fun h : SmoothPoincareConjectureStatement.{0} =>
          threeSphere_self_homeomorph_payload_of_smooth_statement_and_pathQuotientSubsingletonStatement
            (threeSphere_pathQuotientSubsingletonStatement_of_basedLoopNullhomotopyStatement
              hBased)
            h) := by
  funext hBased h
  apply Subsingleton.elim

/--
If the canonical 3-dimensional topological Poincare statement is available as a
proof-bearing theorem, then it proves this project's target proposition.

This theorem deliberately takes the canonical statement as an explicit argument;
it does not use mathlib's current reserved theorem declaration.
-/
theorem poincare_statement_of_canonical_three_sphere_statement
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    PoincareConjectureStatement.{u} := by
  intro M _ _ _ _ _
  exact h M

/--
The canonical 3-dimensional topological Poincare statement exposes both the
project target and the universe-indexed completion criterion as a single
payload.
-/
theorem poincare_payload_of_canonical_three_sphere_statement
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let target : PoincareConjectureStatement.{u} :=
    poincare_statement_of_canonical_three_sphere_statement h
  exact poincare_completion_payload_of_poincareConjectureStatement target

/--
The canonical 3-dimensional topological Poincare statement also discharges the
explicit universe-indexed completion criterion.
-/
theorem completion_criterion_of_canonical_three_sphere_statement
    (witness : Type u)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    CompletionCriterionAtUniverse witness := by
  rcases poincare_payload_of_canonical_three_sphere_statement h with
    ⟨_target, criterion⟩
  exact criterion witness

/--
A proof of the project target statement exposes the canonical topological
3-sphere statement shape.
-/
theorem canonical_three_sphere_statement_of_poincare_statement
    (h : PoincareConjectureStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  h

/--
The project completion payload exposes the canonical topological 3-sphere
statement shape.
-/
theorem canonical_three_sphere_statement_of_poincare_payload
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincareConjectureStatement_of_poincare_completion_payload payload)

/--
The canonical topological 3-sphere statement is equivalent to the project
completion payload.
-/
theorem canonical_three_sphere_statement_iff_poincare_completion_payload :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) ↔
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness :=
  poincareConjectureStatement_iff_canonical_three_sphere_statement.symm.trans
    poincareConjectureStatement_iff_poincare_completion_payload

/--
The explicit universe-indexed completion criterion exposes the canonical
topological 3-sphere statement shape.
-/
theorem canonical_three_sphere_statement_of_completionCriterionAtUniverse
    (witness : Type u) (criterion : CompletionCriterionAtUniverse witness) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincareConjectureStatement_of_completionCriterionAtUniverse
      witness criterion)

/--
The canonical topological 3-sphere statement is equivalent to the explicit
universe-indexed completion criterion.
-/
theorem canonical_three_sphere_statement_iff_completionCriterionAtUniverse
    (witness : Type u) :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) ↔
      CompletionCriterionAtUniverse witness :=
  poincareConjectureStatement_iff_canonical_three_sphere_statement.symm.trans
    (completionCriterionAtUniverse_iff_poincareConjectureStatement witness).symm

/--
If the canonical 3-dimensional smooth Poincare statement is available as a
proof-bearing theorem, then it proves this project's smooth target proposition.

This theorem deliberately takes the canonical statement as an explicit argument;
it does not use mathlib's current reserved theorem declaration.
-/
theorem smooth_statement_of_canonical_three_sphere_statement
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    SmoothPoincareConjectureStatement.{u} := by
  intro M _ _ _ _ _ _
  exact h M

/--
A proof of the project smooth target statement exposes the canonical smooth
3-sphere statement shape.
-/
theorem canonical_smooth_three_sphere_statement_of_smooth_statement
    (h : SmoothPoincareConjectureStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) :=
  h

/--
The canonical smooth 3-sphere statement shape is equivalent to the project smooth
target statement.
-/
theorem canonical_smooth_three_sphere_statement_iff_smooth_statement :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) ↔
      SmoothPoincareConjectureStatement.{u} :=
  smoothPoincareConjectureStatement_iff_canonical_smooth_three_sphere_statement.symm

/--
The project smooth target also exposes the reverse canonical smooth statement
shape, where the standard 3-sphere is the source of the diffeomorphism.
-/
theorem reverse_canonical_smooth_three_sphere_statement_of_smooth_statement
    (h : SmoothPoincareConjectureStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) := by
  intro M _ _ _ _ _ _
  exact threeSphere_diffeomorph_of_diffeomorph_to_threeSphere (h M)

/--
The reverse canonical smooth statement proves this project's smooth target
statement by inverting each supplied diffeomorphism.
-/
theorem smooth_statement_of_reverse_canonical_smooth_three_sphere_statement
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    SmoothPoincareConjectureStatement.{u} := by
  intro M _ _ _ _ _ _
  exact diffeomorph_to_threeSphere_of_threeSphere_diffeomorph (h M)

/--
The reverse canonical smooth statement also exposes the forward canonical
smooth 3-sphere statement shape.
-/
theorem canonical_smooth_three_sphere_statement_of_reverse_canonical_smooth_three_sphere_statement
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) :=
  canonical_smooth_three_sphere_statement_of_smooth_statement
    (smooth_statement_of_reverse_canonical_smooth_three_sphere_statement h)

/--
The reverse canonical smooth statement shape is equivalent to the project smooth
target statement.
-/
theorem reverse_canonical_smooth_three_sphere_statement_iff_smooth_statement :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) ↔
      SmoothPoincareConjectureStatement.{u} := by
  constructor
  · exact smooth_statement_of_reverse_canonical_smooth_three_sphere_statement
  · exact reverse_canonical_smooth_three_sphere_statement_of_smooth_statement

/--
The two canonical smooth statement shapes are equivalent; the difference is
only the side on which the standard 3-sphere is written.
-/
theorem canonical_smooth_three_sphere_statement_iff_reverse_canonical_smooth_three_sphere_statement :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) ↔
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) := by
  constructor
  · intro h M _ _ _ _ _ _
    exact threeSphere_diffeomorph_of_diffeomorph_to_threeSphere (h M)
  · intro h M _ _ _ _ _ _
    exact diffeomorph_to_threeSphere_of_threeSphere_diffeomorph (h M)

/--
If every target topological 3-manifold has the smooth structure required by the
smooth Poincare statement, then the smooth statement implies the topological
target statement.

This is conditional assembly only: it does not prove the smooth Poincare
statement or the smoothability input.
-/
theorem poincare_statement_of_smooth_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    PoincareConjectureStatement.{u} := by
  intro M _ _ _ _ _
  letI : IsManifold (𝓡 3) ∞ M := smoothable M
  exact homeomorph_of_diffeomorph_three_sphere (smoothStatement M)

/--
The smooth Poincare statement plus the smoothability input exposes the
canonical topological 3-sphere statement shape.
-/
theorem canonical_three_sphere_statement_of_smooth_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_smooth_statement smoothable smoothStatement)

/--
The smooth Poincare statement plus the smoothability input exposes the
topological target and completion criterion as one payload.
-/
theorem poincare_payload_of_smooth_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let target : PoincareConjectureStatement.{u} :=
    poincare_statement_of_smooth_statement smoothable smoothStatement
  exact poincare_completion_payload_of_poincareConjectureStatement target

/--
The smooth Poincare statement plus the smoothability input discharges the
explicit universe-indexed completion criterion.
-/
theorem completion_criterion_of_smooth_statement
    (witness : Type u)
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    CompletionCriterionAtUniverse witness := by
  rcases poincare_payload_of_smooth_statement smoothable smoothStatement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The canonical smooth 3-dimensional Poincare statement, together with the
smoothability input, proves the project's topological target statement.

This is the direct assembly path to use if mathlib's smooth 3D statement becomes
proof-bearing before the local Ricci-flow dependency package is completed.
-/
theorem poincare_statement_of_canonical_smooth_three_sphere_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    PoincareConjectureStatement.{u} := by
  rcases poincare_payload_of_smooth_statement smoothable
      (smooth_statement_of_canonical_three_sphere_statement h) with
    ⟨target, _criterion⟩
  exact target

/--
The canonical smooth 3-dimensional Poincare statement, together with
smoothability, exposes the canonical topological 3-sphere statement shape.
-/
theorem canonical_three_sphere_statement_of_canonical_smooth_three_sphere_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_smooth_statement smoothable
    (smooth_statement_of_canonical_three_sphere_statement h)

/--
The canonical smooth 3-dimensional Poincare statement, together with
smoothability, exposes the topological target and completion criterion as one
payload.
-/
theorem poincare_payload_of_canonical_smooth_three_sphere_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let smoothStatement : SmoothPoincareConjectureStatement.{u} :=
    smooth_statement_of_canonical_three_sphere_statement h
  rcases poincare_payload_of_smooth_statement smoothable smoothStatement with
    ⟨target, criterion⟩
  exact ⟨target, criterion⟩

/--
The canonical smooth 3-dimensional Poincare statement, together with
smoothability, also discharges the explicit completion criterion.
-/
theorem completion_criterion_of_canonical_smooth_three_sphere_statement
    (witness : Type u)
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    CompletionCriterionAtUniverse witness := by
  rcases poincare_payload_of_canonical_smooth_three_sphere_statement
      smoothable h with
    ⟨_target, criterion⟩
  exact criterion witness

/--
If a proof-bearing smooth statement produces diffeomorphisms from the standard
3-sphere to each target manifold, then the smoothability input still assembles
the project's topological target statement.

This is conditional assembly only: it does not prove the reverse smooth
Poincare statement or the smoothability input.
-/
theorem poincare_statement_of_reverse_smooth_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    PoincareConjectureStatement.{u} := by
  intro M _ _ _ _ _
  letI : IsManifold (𝓡 3) ∞ M := smoothable M
  exact homeomorph_of_threeSphere_diffeomorph
    (reverseSmoothStatement M)

/--
The reverse-direction smooth statement plus smoothability exposes the canonical
topological 3-sphere statement shape.
-/
theorem canonical_three_sphere_statement_of_reverse_smooth_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere) :=
  canonical_three_sphere_statement_of_poincare_statement
    (poincare_statement_of_reverse_smooth_statement
      smoothable reverseSmoothStatement)

/--
The reverse-direction smooth statement plus smoothability exposes the
topological target and completion criterion as one payload.
-/
theorem poincare_payload_of_reverse_smooth_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    ∃ _target : PoincareConjectureStatement.{u},
      ∀ witness : Type u, CompletionCriterionAtUniverse witness := by
  let target : PoincareConjectureStatement.{u} :=
    poincare_statement_of_reverse_smooth_statement
      smoothable reverseSmoothStatement
  exact poincare_completion_payload_of_poincareConjectureStatement target

/--
The reverse-direction smooth statement plus smoothability discharges the
explicit universe-indexed completion criterion.
-/
theorem completion_criterion_of_reverse_smooth_statement
    (witness : Type u)
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    CompletionCriterionAtUniverse witness := by
  rcases poincare_payload_of_reverse_smooth_statement
      smoothable reverseSmoothStatement with
    ⟨_target, criterion⟩
  exact criterion witness

/--
The diffeomorphism-to-homeomorphism bridge is exactly the projection through
`Diffeomorph.toHomeomorph`.
-/
theorem homeomorph_of_diffeomorph_three_sphere_eq
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    homeomorph_of_diffeomorph_three_sphere (M := M) =
      (fun witness => by
        rcases witness with ⟨h⟩
        exact ⟨h.toHomeomorph⟩) := by
  apply Subsingleton.elim

/--
The reverse-direction diffeomorphism-to-homeomorphism bridge inverts the
diffeomorphism and forgets it to a homeomorphism.
-/
theorem homeomorph_of_threeSphere_diffeomorph_eq
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    homeomorph_of_threeSphere_diffeomorph (M := M) =
      (fun witness => by
        rcases witness with ⟨h⟩
        exact ⟨h.symm.toHomeomorph⟩) := by
  apply Subsingleton.elim

/-- The forward smooth-direction inversion bridge uses `Diffeomorph.symm`. -/
theorem threeSphere_diffeomorph_of_diffeomorph_to_threeSphere_eq
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    threeSphere_diffeomorph_of_diffeomorph_to_threeSphere (M := M) =
      (fun witness => by
        rcases witness with ⟨h⟩
        exact ⟨h.symm⟩) := by
  apply Subsingleton.elim

/-- The reverse smooth-direction inversion bridge uses `Diffeomorph.symm`. -/
theorem diffeomorph_to_threeSphere_of_threeSphere_diffeomorph_eq
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    diffeomorph_to_threeSphere_of_threeSphere_diffeomorph (M := M) =
      (fun witness => by
        rcases witness with ⟨h⟩
        exact ⟨h.symm⟩) := by
  apply Subsingleton.elim

/--
The smooth target-side equivalence is the pair of named inverse-diffeomorphism
conversions.
-/
theorem diffeomorph_to_threeSphere_iff_threeSphere_diffeomorph_eq
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    (diffeomorph_to_threeSphere_iff_threeSphere_diffeomorph :
      Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere) ↔
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) =
      (by
        constructor
        · exact threeSphere_diffeomorph_of_diffeomorph_to_threeSphere
        · exact diffeomorph_to_threeSphere_of_threeSphere_diffeomorph) := by
  apply Subsingleton.elim

/--
The canonical topological statement proves the project target by direct
specialization.
-/
theorem poincare_statement_of_canonical_three_sphere_statement_eq
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    poincare_statement_of_canonical_three_sphere_statement h =
      (by
        intro M _ _ _ _ _
        exact h M) := by
  apply Subsingleton.elim

/--
The canonical topological statement payload is built from its named project
target projection.
-/
theorem poincare_payload_of_canonical_three_sphere_statement_eq
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    poincare_payload_of_canonical_three_sphere_statement h =
      (by
        let target : PoincareConjectureStatement.{u} :=
          poincare_statement_of_canonical_three_sphere_statement h
        exact poincare_completion_payload_of_poincareConjectureStatement target) := by
  apply Subsingleton.elim

/--
The canonical topological statement criterion is selected from the named
payload.
-/
theorem completion_criterion_of_canonical_three_sphere_statement_eq
    (witness : Type u)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    completion_criterion_of_canonical_three_sphere_statement witness h =
      (by
        rcases poincare_payload_of_canonical_three_sphere_statement h with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The project target exposes the canonical topological statement by the identity
projection.
-/
theorem canonical_three_sphere_statement_of_poincare_statement_eq
    (h : PoincareConjectureStatement.{u}) :
    canonical_three_sphere_statement_of_poincare_statement h = h := by
  apply Subsingleton.elim

/--
The project payload exposes the canonical topological statement through its
project target projection.
-/
theorem canonical_three_sphere_statement_of_poincare_payload_eq
    (payload :
      ∃ _target : PoincareConjectureStatement.{u},
        ∀ witness : Type u, CompletionCriterionAtUniverse witness) :
    canonical_three_sphere_statement_of_poincare_payload payload =
      canonical_three_sphere_statement_of_poincare_statement
        (poincareConjectureStatement_of_poincare_completion_payload
          payload) := by
  apply Subsingleton.elim

/--
The canonical topological statement/completion-payload iff is the composition
of the statement iff with the project completion-payload iff.
-/
theorem canonical_three_sphere_statement_iff_poincare_completion_payload_eq :
    canonical_three_sphere_statement_iff_poincare_completion_payload =
      poincareConjectureStatement_iff_canonical_three_sphere_statement.symm.trans
        poincareConjectureStatement_iff_poincare_completion_payload := by
  apply Subsingleton.elim

/--
The explicit completion criterion exposes the canonical statement through its
project target projection.
-/
theorem canonical_three_sphere_statement_of_completionCriterionAtUniverse_eq
    (witness : Type u) (criterion : CompletionCriterionAtUniverse witness) :
    canonical_three_sphere_statement_of_completionCriterionAtUniverse
      witness criterion =
      canonical_three_sphere_statement_of_poincare_statement
        (poincareConjectureStatement_of_completionCriterionAtUniverse
          witness criterion) := by
  apply Subsingleton.elim

/--
The canonical topological statement/completion-criterion iff is the composition
of the statement iff with the criterion iff.
-/
theorem canonical_three_sphere_statement_iff_completionCriterionAtUniverse_eq
    (witness : Type u) :
    canonical_three_sphere_statement_iff_completionCriterionAtUniverse
      witness =
      poincareConjectureStatement_iff_canonical_three_sphere_statement.symm.trans
        (completionCriterionAtUniverse_iff_poincareConjectureStatement
          witness).symm := by
  apply Subsingleton.elim

/--
The canonical smooth statement proves the project smooth target by direct
specialization.
-/
theorem smooth_statement_of_canonical_three_sphere_statement_eq
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    smooth_statement_of_canonical_three_sphere_statement h =
      (by
        intro M _ _ _ _ _ _
        exact h M) := by
  apply Subsingleton.elim

/--
The project smooth target exposes the canonical smooth statement by the
identity projection.
-/
theorem canonical_smooth_three_sphere_statement_of_smooth_statement_eq
    (h : SmoothPoincareConjectureStatement.{u}) :
    canonical_smooth_three_sphere_statement_of_smooth_statement h = h := by
  apply Subsingleton.elim

/--
The canonical smooth statement iff is the reverse of the statement-layer
canonical smooth iff.
-/
theorem canonical_smooth_three_sphere_statement_iff_smooth_statement_eq :
    canonical_smooth_three_sphere_statement_iff_smooth_statement =
      smoothPoincareConjectureStatement_iff_canonical_smooth_three_sphere_statement.symm := by
  apply Subsingleton.elim

/--
The project smooth statement exposes the reverse canonical smooth statement by
inverting the supplied diffeomorphism.
-/
theorem reverse_canonical_smooth_three_sphere_statement_of_smooth_statement_eq
    (h : SmoothPoincareConjectureStatement.{u}) :
    reverse_canonical_smooth_three_sphere_statement_of_smooth_statement h =
      (by
        intro M _ _ _ _ _ _
        exact threeSphere_diffeomorph_of_diffeomorph_to_threeSphere
          (h M)) := by
  apply Subsingleton.elim

/--
The reverse canonical smooth statement proves the project smooth statement by
inverting the supplied diffeomorphism.
-/
theorem smooth_statement_of_reverse_canonical_smooth_three_sphere_statement_eq
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    smooth_statement_of_reverse_canonical_smooth_three_sphere_statement h =
      (by
        intro M _ _ _ _ _ _
        exact diffeomorph_to_threeSphere_of_threeSphere_diffeomorph
          (h M)) := by
  apply Subsingleton.elim

/--
The forward canonical smooth statement projection from the reverse shape
factors through the named project smooth statement projection.
-/
theorem canonical_smooth_three_sphere_statement_of_reverse_canonical_smooth_three_sphere_statement_eq
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    canonical_smooth_three_sphere_statement_of_reverse_canonical_smooth_three_sphere_statement h =
      canonical_smooth_three_sphere_statement_of_smooth_statement
        (smooth_statement_of_reverse_canonical_smooth_three_sphere_statement
          h) := by
  apply Subsingleton.elim

/--
The reverse canonical smooth/project smooth iff is the pair of named statement
projections.
-/
theorem reverse_canonical_smooth_three_sphere_statement_iff_smooth_statement_eq :
    reverse_canonical_smooth_three_sphere_statement_iff_smooth_statement =
      (by
        constructor
        · exact smooth_statement_of_reverse_canonical_smooth_three_sphere_statement
        · exact reverse_canonical_smooth_three_sphere_statement_of_smooth_statement) := by
  apply Subsingleton.elim

/--
The forward/reverse canonical smooth iff is the pair of named
inverse-diffeomorphism conversions.
-/
theorem canonical_smooth_three_sphere_statement_iff_reverse_canonical_smooth_three_sphere_statement_eq :
    canonical_smooth_three_sphere_statement_iff_reverse_canonical_smooth_three_sphere_statement =
      (by
        constructor
        · intro h M _ _ _ _ _ _
          exact threeSphere_diffeomorph_of_diffeomorph_to_threeSphere
            (h M)
        · intro h M _ _ _ _ _ _
          exact diffeomorph_to_threeSphere_of_threeSphere_diffeomorph
            (h M)) := by
  apply Subsingleton.elim

/--
The smooth statement and smoothability input prove the project target by
specializing the supplied smooth structure and forgetting the diffeomorphism.
-/
theorem poincare_statement_of_smooth_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    poincare_statement_of_smooth_statement smoothable smoothStatement =
      (by
        intro M _ _ _ _ _
        letI : IsManifold (𝓡 3) ∞ M := smoothable M
        exact homeomorph_of_diffeomorph_three_sphere (smoothStatement M)) := by
  apply Subsingleton.elim

/--
The smooth statement canonical topological projection factors through the named
project target projection.
-/
theorem canonical_three_sphere_statement_of_smooth_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    canonical_three_sphere_statement_of_smooth_statement
      smoothable smoothStatement =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_smooth_statement smoothable smoothStatement) := by
  apply Subsingleton.elim

/--
The smooth statement project payload is built from the named smooth project
target projection.
-/
theorem poincare_payload_of_smooth_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    poincare_payload_of_smooth_statement smoothable smoothStatement =
      (by
        let target : PoincareConjectureStatement.{u} :=
          poincare_statement_of_smooth_statement smoothable smoothStatement
        exact poincare_completion_payload_of_poincareConjectureStatement
          target) := by
  apply Subsingleton.elim

/--
The smooth statement completion criterion is selected from the named smooth
project payload.
-/
theorem completion_criterion_of_smooth_statement_eq
    (witness : Type u)
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    completion_criterion_of_smooth_statement
      witness smoothable smoothStatement =
      (by
        rcases poincare_payload_of_smooth_statement
            smoothable smoothStatement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The canonical smooth statement project target factors through the induced
project smooth statement and its named smooth payload.
-/
theorem poincare_statement_of_canonical_smooth_three_sphere_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    poincare_statement_of_canonical_smooth_three_sphere_statement
      smoothable h =
      (by
        rcases poincare_payload_of_smooth_statement smoothable
            (smooth_statement_of_canonical_three_sphere_statement h) with
          ⟨target, _criterion⟩
        exact target) := by
  apply Subsingleton.elim

/--
The canonical smooth statement canonical topological projection factors through
the induced project smooth statement.
-/
theorem canonical_three_sphere_statement_of_canonical_smooth_three_sphere_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    canonical_three_sphere_statement_of_canonical_smooth_three_sphere_statement
      smoothable h =
      canonical_three_sphere_statement_of_smooth_statement smoothable
        (smooth_statement_of_canonical_three_sphere_statement h) := by
  apply Subsingleton.elim

/--
The canonical smooth statement project payload is selected from the induced
project smooth statement and the smooth assembly payload.
-/
theorem poincare_payload_of_canonical_smooth_three_sphere_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    poincare_payload_of_canonical_smooth_three_sphere_statement
      smoothable h =
      (by
        let smoothStatement : SmoothPoincareConjectureStatement.{u} :=
          smooth_statement_of_canonical_three_sphere_statement h
        rcases poincare_payload_of_smooth_statement
            smoothable smoothStatement with
          ⟨target, criterion⟩
        exact ⟨target, criterion⟩) := by
  apply Subsingleton.elim

/--
The canonical smooth statement completion criterion is selected from the named
canonical smooth project payload.
-/
theorem completion_criterion_of_canonical_smooth_three_sphere_statement_eq
    (witness : Type u)
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    completion_criterion_of_canonical_smooth_three_sphere_statement
      witness smoothable h =
      (by
        rcases poincare_payload_of_canonical_smooth_three_sphere_statement
            smoothable h with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The reverse smooth statement and smoothability input prove the project target
by specializing the supplied smooth structure, inverting the diffeomorphism,
and forgetting it to a homeomorphism.
-/
theorem poincare_statement_of_reverse_smooth_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    poincare_statement_of_reverse_smooth_statement
      smoothable reverseSmoothStatement =
      (by
        intro M _ _ _ _ _
        letI : IsManifold (𝓡 3) ∞ M := smoothable M
        exact homeomorph_of_threeSphere_diffeomorph
          (reverseSmoothStatement M)) := by
  apply Subsingleton.elim

/--
The reverse smooth statement canonical topological projection factors through
the named project target projection.
-/
theorem canonical_three_sphere_statement_of_reverse_smooth_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    canonical_three_sphere_statement_of_reverse_smooth_statement
      smoothable reverseSmoothStatement =
      canonical_three_sphere_statement_of_poincare_statement
        (poincare_statement_of_reverse_smooth_statement
          smoothable reverseSmoothStatement) := by
  apply Subsingleton.elim

/--
The reverse smooth statement project payload is built from the named reverse
smooth project target projection.
-/
theorem poincare_payload_of_reverse_smooth_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    poincare_payload_of_reverse_smooth_statement
      smoothable reverseSmoothStatement =
      (by
        let target : PoincareConjectureStatement.{u} :=
          poincare_statement_of_reverse_smooth_statement
            smoothable reverseSmoothStatement
        exact poincare_completion_payload_of_poincareConjectureStatement
          target) := by
  apply Subsingleton.elim

/--
The reverse smooth statement completion criterion is selected from the named
reverse smooth project payload.
-/
theorem completion_criterion_of_reverse_smooth_statement_eq
    (witness : Type u)
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    completion_criterion_of_reverse_smooth_statement
      witness smoothable reverseSmoothStatement =
      (by
        rcases poincare_payload_of_reverse_smooth_statement
            smoothable reverseSmoothStatement with
          ⟨_target, criterion⟩
        exact criterion witness) := by
  apply Subsingleton.elim

/--
The canonical topological statement is a direct conditional gate for the
reserved final theorem name.
-/
theorem poincare_conjecture_of_canonical_three_sphere_statement
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_canonical_three_sphere_statement h

/--
The canonical topological reserved-name route is the existing project statement
projection.
-/
theorem poincare_conjecture_of_canonical_three_sphere_statement_eq
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₜ ThreeSphere)) :
    poincare_conjecture_of_canonical_three_sphere_statement h =
      poincare_statement_of_canonical_three_sphere_statement h := by
  apply Subsingleton.elim

/--
The smooth statement plus smoothability is a direct conditional gate for the
reserved final theorem name.
-/
theorem poincare_conjecture_of_smooth_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_smooth_statement smoothable smoothStatement

/--
The smooth reserved-name route is the existing smooth-to-topological project
statement projection.
-/
theorem poincare_conjecture_of_smooth_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (smoothStatement : SmoothPoincareConjectureStatement.{u}) :
    poincare_conjecture_of_smooth_statement smoothable smoothStatement =
      poincare_statement_of_smooth_statement smoothable smoothStatement := by
  apply Subsingleton.elim

/--
The canonical smooth statement plus smoothability is a direct conditional gate
for the reserved final theorem name.
-/
theorem poincare_conjecture_of_canonical_smooth_three_sphere_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_canonical_smooth_three_sphere_statement
    smoothable h

/--
The canonical smooth reserved-name route is the existing canonical smooth
project statement projection.
-/
theorem poincare_conjecture_of_canonical_smooth_three_sphere_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (h : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [SimplyConnectedSpace M] [CompactSpace M],
        Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ ThreeSphere)) :
    poincare_conjecture_of_canonical_smooth_three_sphere_statement
        smoothable h =
      poincare_statement_of_canonical_smooth_three_sphere_statement
        smoothable h := by
  apply Subsingleton.elim

/--
The reverse smooth statement plus smoothability is a direct conditional gate for
the reserved final theorem name.
-/
theorem poincare_conjecture_of_reverse_smooth_statement
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_reverse_smooth_statement
    smoothable reverseSmoothStatement

/--
The reverse smooth reserved-name route is the existing reverse smooth project
statement projection.
-/
theorem poincare_conjecture_of_reverse_smooth_statement_eq
    (smoothable :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M],
          IsManifold (𝓡 3) ∞ M)
    (reverseSmoothStatement :
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        [SimplyConnectedSpace M] [CompactSpace M],
          Nonempty (ThreeSphere ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)) :
    poincare_conjecture_of_reverse_smooth_statement
        smoothable reverseSmoothStatement =
      poincare_statement_of_reverse_smooth_statement
        smoothable reverseSmoothStatement := by
  apply Subsingleton.elim

end Poincare
