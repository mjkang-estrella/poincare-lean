import Poincare.ProofProgress.OnePointTwoPointComplementTopology
import Poincare.ProofProgress.ThreeSphereTwoPointPiOne
import Poincare.TopologyExtraction

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
Distinct compactification points remain distinct after applying the named
homeomorphism to `ThreeSphere`.
-/
theorem onePoint_threeSpace_twoPointComplement_threeSphere_image_distinct
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p) :
    (Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q ≠
      (Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p := by
  intro h
  exact hqp
    ((Classical.choice onePoint_threeSpace_homeomorph_threeSphere).injective h)

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
Transport package from the one-point compactification two-puncture complement
to the corresponding `ThreeSphere` two-puncture complement.  It retains the
source flat-recognition payload and the target complete low-homotopy collapse
payload at the transported basepoint.
-/
structure OnePointThreeSphereTwoPointComplementTransportPayload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) where
  imageDistinct :
    (Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q ≠
      (Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p
  complementHomeomorph :
    (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)
  sourceFlatRecognition :
    OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint
  targetCompleteLowHomotopy :
    ThreeSphereTwoPointComplementCompleteLowHomotopyUniquePayload
      imageDistinct (complementHomeomorph basepoint)
  targetSimplyConnected :
    SimplyConnectedSpace
      (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
          {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
        Set ThreeSphere)
  sourceSimplyConnected :
    SimplyConnectedSpace
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))

/--
The named one-point-to-`ThreeSphere` homeomorphism constructs the complete
two-puncture transport payload.
-/
noncomputable def onePoint_threeSpace_twoPointComplement_transport_payload
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    OnePointThreeSphereTwoPointComplementTransportPayload hqp basepoint := by
  let hImage :=
    onePoint_threeSpace_twoPointComplement_threeSphere_image_distinct hqp
  let complementHomeomorph :=
    onePoint_threeSpace_twoPointComplement_homeomorph_threeSphere_twoPointComplement
      hqp
  exact
    { imageDistinct := hImage
      complementHomeomorph := complementHomeomorph
      sourceFlatRecognition :=
        onePoint_threeSpace_twoPointComplement_flatRecognition_payload
          hqp basepoint
      targetCompleteLowHomotopy :=
        threeSphere_twoPointComplement_completeLowHomotopyUnique_payload
          hImage (complementHomeomorph basepoint)
      targetSimplyConnected :=
        threeSphere_twoPointComplement_simplyConnectedSpace hImage
      sourceSimplyConnected :=
        onePoint_threeSpace_twoPointComplement_simplyConnectedSpace_via_threeSphere
          hqp }

/--
The transport payload exposes the target complete low-homotopy package and the
source flat-recognition package together.
-/
theorem onePoint_threeSpace_twoPointComplement_transport_payload_fields
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    let payload :=
      onePoint_threeSpace_twoPointComplement_transport_payload hqp basepoint
    Nonempty
        (ThreeSphereTwoPointComplementCompleteLowHomotopyUniquePayload
          payload.imageDistinct (payload.complementHomeomorph basepoint)) ∧
      Nonempty
        (OnePointTwoPointComplementFlatRecognitionPayload hqp basepoint) := by
  intro payload
  exact ⟨⟨payload.targetCompleteLowHomotopy⟩, ⟨payload.sourceFlatRecognition⟩⟩

/--
Complete theorem-shaped projection of the transported two-puncture topology
payload.  It exposes the complement homeomorphism, source punctured-Euclidean
recognition, source and target simple-connectedness, and the complete target
low-homotopy collapse fields at the transported basepoint.
-/
theorem onePoint_threeSpace_twoPointComplement_transport_payload_complete_fields
    {p q : OnePoint (EuclideanSpace ℝ (Fin 3))} (hqp : q ≠ p)
    (basepoint :
      (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3))))) :
    let payload :=
      onePoint_threeSpace_twoPointComplement_transport_payload hqp basepoint
    let targetBasepoint := payload.complementHomeomorph basepoint
    Nonempty
        ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
          (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
              {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
            Set ThreeSphere)) ∧
      (∃ puncture : EuclideanSpace ℝ (Fin 3),
        Nonempty
          ((({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ≃ₜ
            ({puncture}ᶜ : Set (EuclideanSpace ℝ (Fin 3))))) ∧
      SimplyConnectedSpace
        (({p} ∪ {q})ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin 3)))) ∧
      SimplyConnectedSpace
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere) ∧
      ConnectedSpace
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere) ∧
      Nonempty
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere) ∧
      Nonempty
        (Unique
          (FundamentalGroup
            (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
              Set ThreeSphere)
            targetBasepoint)) ∧
      Nonempty
        (Unique
          (HomotopyGroup.Pi 1
            (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
              Set ThreeSphere)
            targetBasepoint)) ∧
      Nonempty
        (Unique
          (HomotopyGroup.Pi 0
            (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
              Set ThreeSphere)
            targetBasepoint)) ∧
      Nonempty
        (Unique
          (ZerothHomotopy
            (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
                {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
              Set ThreeSphere))) ∧
      (∀ x y :
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere),
          Nonempty (Path x y)) ∧
      (∀ x :
        (({(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) p} ∪
            {(Classical.choice onePoint_threeSpace_homeomorph_threeSphere) q})ᶜ :
          Set ThreeSphere),
          pathComponent x = Set.univ) := by
  intro payload targetBasepoint
  exact
    ⟨ ⟨payload.complementHomeomorph⟩
    , payload.sourceFlatRecognition.puncturedEuclideanChart
    , payload.sourceSimplyConnected
    , payload.targetSimplyConnected
    , payload.targetCompleteLowHomotopy.connected
    , payload.targetCompleteLowHomotopy.nonempty
    , ⟨payload.targetCompleteLowHomotopy.fundamentalGroupUnique⟩
    , ⟨payload.targetCompleteLowHomotopy.piOneUnique⟩
    , ⟨payload.targetCompleteLowHomotopy.piZeroUnique⟩
    , ⟨payload.targetCompleteLowHomotopy.zerothUnique⟩
    , payload.targetCompleteLowHomotopy.pathNonempty
    , payload.targetCompleteLowHomotopy.pathComponentEqUniv
    ⟩

end Poincare
