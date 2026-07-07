Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-68: THE INSTANTIATION — hosted data into the speed-generic consumer

Context: `harness/reports/M5-rigid-67_done.md` (READ FIRST). THE SPEED-GENERIC LAYER IS COMPLETE (`SpeedGeneric.lean`, 1839 lines): speed-s oscillator, norm system, pinned solutions, source/target endpoint packages, `SpeedPackage` bridges, the common-speed feed + local-isometry consumer — the hosted transverse scale `sin(sT)²/(sT)²` matches `CartanScaleGeneric`'s feed shape natively. THE TASK: INSTANTIATE at the actual hosted data — the hosted `(u,T)` construction (`CartanHomogeneity.lean`), the actual cascade families (`CartanCascade.lean`), the speed values (`SpeedPackage.lean`), the interval discharges (`CartanIsometryTheorem.lean` source side; `TargetPackage.lean` sphere side), the alignment (`TangentAlignment`) — feed the speed-generic packages' hypotheses, produce the common-speed feeds, apply the consumer. 🎯 THE DELIVERABLE: `cartanMap_isLocalIsometry`-shaped — hypotheses ONLY `HasConstantSectionalCurvature3 g 1` + instances + anchors + alignment; the chart-metric pullback equality on a punctured shrunk normal ball. If ONE hypothesis resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/TheLocalIsometry.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-68_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.TheLocalIsometry` and report the actual result. Commit your work.
