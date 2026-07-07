Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-1: the globalization skeleton — covering maps and simple connectedness

Context: the rigidity endgame (`UnitConstantCurvatureSphereRecognition3`, `SphereTheorem.lean`) will conclude via: a LOCAL ISOMETRY `Φ : M → RoundSphere3` (in flight, rigid-8..10: local homeo on uniform normal balls — `UniformNormalRadius.lean` gives the uniform radius; `MetricCompleteness.lean` completeness) promotes to a COVERING MAP (compact + uniform-radius local homeo), and a covering of a SIMPLY CONNECTED space by a CONNECTED space is a homeomorphism. This task builds the ABSTRACT TOPOLOGY skeleton, self-contained.

Deliverables:
1. REPORT-FIRST in `harness/reports/M5-glob-1_assets.md`: inventory Mathlib's covering-space theory (`Mathlib/Topology/Covering*.lean`: `IsCoveringMap`, evenly-covered, path/homotopy lifting; `SimplyConnectedSpace`; fundamental groupoid): what exists for (a) "local homeo + (uniform/compactness condition) ⟹ IsCoveringMap", (b) "IsCoveringMap onto simply connected + total space connected ⟹ homeomorphism" (or injective/bijective + open ⟹ homeo). Honest verdict per piece.
2. FIRST LEMMAS, in a NEW file `Poincare/Global/CoveringSkeleton.lean` (do NOT edit existing files, incl. `Poincare.lean`): prove what closes NOW at the abstract level — target shapes: `theorem isHomeomorph_of_isCoveringMap_simplyConnected`-shaped (covering of simply connected connected-fibers... the classical statement: a covering map onto a simply connected, locally path-connected space with connected total space is a homeomorphism — check what Mathlib's `IsCoveringMap` API + `SimplyConnectedSpace` gives; the sphere and closed manifolds are locally path-connected — instances may need assembling); and/or the surjectivity lemma (a local homeo with open+closed image onto a connected space is surjective — clopen argument, elementary). Deliver the pieces that genuinely close; isolate the rest.
3. Report `harness/reports/M5-glob-1_{done|blocked}.md` (may merge with assets): the remaining glue to consume the future local-isometry statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.CoveringSkeleton` and report the actual result. Commit your work.
