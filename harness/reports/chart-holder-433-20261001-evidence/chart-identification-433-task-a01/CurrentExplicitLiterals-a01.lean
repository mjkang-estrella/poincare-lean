import Lean
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.MeanValue
open Lean Elab Command Meta
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped Manifold
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [IsManifold.{u_1, u_2, u_3, u_4} I (1 : WithTop.{0} ENat) M] (X Y : (y : M) → TangentSpace.{u_2, u_1, u_3, u_4} I y) (x : M), Eq.{u_2 + 1} (VectorField.mlieBracket.{u_1, u_3, u_2, u_4} I X Y x) (VectorField.lieBracketWithin.{u_1, u_2} 𝕜 (VectorField.mpullbackWithin.{u_1, u_2, u_2, u_2, u_3, u_2, u_4} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) I (↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) X (Set.range.{u_2, u_3 + 1} ↑I)) (VectorField.mpullbackWithin.{u_1, u_2, u_2, u_2, u_3, u_2, u_4} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) I (↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) Y (Set.range.{u_2, u_3 + 1} ↑I)) (Set.range.{u_2, u_3 + 1} ↑I) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x) x))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal mlieBracket_apply_chart"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop mlieBracket_apply_chart"
  logInfo "CURRENT_LITERAL_ELAB_OK:mlieBracket_apply_chart"

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [IsManifold.{u_1, u_2, u_3, u_4} I (1 : WithTop.{0} ENat) M] (X : (y : M) → TangentSpace.{u_2, u_1, u_3, u_4} I y) (x : M), Eq.{u_2 + 1} (VectorField.mpullbackWithin.{u_1, u_2, u_2, u_2, u_3, u_2, u_4} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) I (↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) X (Set.range.{u_2, u_3 + 1} ↑I) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x) x)) (X x)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal mpullbackWithin_extChartAt_symm_self"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop mpullbackWithin_extChartAt_symm_self"
  logInfo "CURRENT_LITERAL_ELAB_OK:mpullbackWithin_extChartAt_symm_self"

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [ModelWithCorners.Boundaryless.{u_1, u_2, u_3} I] {f : M → 𝕜} {x : M}, MDifferentiableAt.{u_1, u_2, u_3, u_4, u_1, u_1, u_1} I (modelWithCornersSelf.{u_1, u_1} 𝕜 𝕜) f x → ∀ (v : TangentSpace.{u_2, u_1, u_3, u_4} I x), Eq.{u_1 + 1} ((mvfderiv I f x) v) ((fderiv.{u_1, u_2, u_1} 𝕜 (Function.comp.{u_2 + 1, u_4 + 1, u_1 + 1} f ↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x) x)) v)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal extDerivFun_apply_chart"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop extDerivFun_apply_chart"
  logInfo "CURRENT_LITERAL_ELAB_OK:extDerivFun_apply_chart"

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [IsManifold.{u_1, u_2, u_3, u_4} I (1 : WithTop.{0} ENat) M] [ModelWithCorners.Boundaryless.{u_1, u_2, u_3} I] {f : M → 𝕜} {x₀ y : M}, Membership.mem.{u_4, u_4} (PartialEquiv.source.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x₀)) y → MDifferentiableAt.{u_1, u_2, u_3, u_4, u_1, u_1, u_1} I (modelWithCornersSelf.{u_1, u_1} 𝕜 𝕜) f y → ∀ (v : TangentSpace.{u_2, u_1, u_3, u_4} I y), Eq.{u_1 + 1} ((mvfderiv I f y) v) ((fderiv.{u_1, u_2, u_1} 𝕜 (Function.comp.{u_2 + 1, u_4 + 1, u_1 + 1} f ↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x₀))) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x₀) y)) ((mfderiv.{u_1, u_2, u_3, u_4, u_2, u_2, u_2} I (modelWithCornersSelf.{u_1, u_2} 𝕜 E) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x₀)) y) v))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal extDerivFun_apply_fixed_chart"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop extDerivFun_apply_fixed_chart"
  logInfo "CURRENT_LITERAL_ELAB_OK:extDerivFun_apply_fixed_chart"

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_5} [inst : NormedAddCommGroup.{u_5} E] [inst_1 : NormedSpace.{0, u_5} Real E] {H : Type u_6} [inst_2 : TopologicalSpace.{u_6} H] {I : ModelWithCorners.{0, u_5, u_6} Real E H} {M : Type u_7} [inst_3 : TopologicalSpace.{u_7} M] [inst_4 : ChartedSpace.{u_6, u_7} H M] [IsManifold.{0, u_5, u_6, u_7} I (1 : WithTop.{0} ENat) M] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I] {f : M → Real}, (∀ (x : M), MDifferentiableAt.{0, u_5, u_6, u_7, 0, 0, 0} I (modelWithCornersSelf.{0, 0} Real Real) f x) → (∀ (x : M) (w : TangentSpace.{u_5, 0, u_6, u_7} I x), Eq.{1} ((mvfderiv I f x) w) (0 : Real)) → IsLocallyConstant.{u_7, 0} f" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal isLocallyConstant_of_extDerivFun_eq_zero"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop isLocallyConstant_of_extDerivFun_eq_zero"
  logInfo "CURRENT_LITERAL_ELAB_OK:isLocallyConstant_of_extDerivFun_eq_zero"

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [inst_5 : IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {X Y : (y : N) → TangentSpace.{u_5, 0, u_6, u_7} I' y} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (X y)) x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (Y y)) x → Eq.{1} ((mvfderiv I' f x) (VectorField.mlieBracket.{0, u_6, u_5, u_7} I' X Y x)) (HSub.hSub.{0, 0, 0} ((fderiv.{0, u_5, 0} Real (fun (z : E') => (fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) z) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) Y z)) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) x)) (X x)) ((fderiv.{0, u_5, 0} Real (fun (z : E') => (fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) z) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) X z)) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) x)) (Y x)))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal extDerivFun_apply_mlieBracket_chart"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop extDerivFun_apply_mlieBracket_chart"
  logInfo "CURRENT_LITERAL_ELAB_OK:extDerivFun_apply_mlieBracket_chart"

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {x y : N}, Membership.mem.{u_7, u_7} (PartialEquiv.source.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x)) y → ∀ (U : (z : N) → TangentSpace.{u_5, 0, u_6, u_7} I' z), Eq.{u_5 + 1} (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) U (↑(extChartAt.{0, u_5, u_7, u_6} I' x) y)) ((mfderiv.{0, u_5, u_6, u_7, u_5, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E') (↑(extChartAt.{0, u_5, u_7, u_6} I' x)) y) (U y))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal mpullback_extChartAt_symm_apply"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop mpullback_extChartAt_symm_apply"
  logInfo "CURRENT_LITERAL_ELAB_OK:mpullback_extChartAt_symm_apply"

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → ∀ (U : (z : N) → TangentSpace.{u_5, 0, u_6, u_7} I' z), Filter.Eventually.{u_7} (fun (y : N) => Eq.{1} ((mvfderiv I' f y) (U y)) ((fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) y)) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) U (↑(extChartAt.{0, u_5, u_7, u_6} I' x) y)))) (nhds.{u_7} x)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal extDerivFun_section_eventually_chart"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop extDerivFun_section_eventually_chart"
  logInfo "CURRENT_LITERAL_ELAB_OK:extDerivFun_section_eventually_chart"

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [inst_5 : IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {U : (y : N) → TangentSpace.{u_5, 0, u_6, u_7} I' y} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (U y)) x → ∀ (v : TangentSpace.{u_5, 0, u_6, u_7} I' x), Eq.{1} ((mvfderiv I' (fun (y : N) => (mvfderiv I' f y) (U y)) x) v) ((fderiv.{0, u_5, 0} Real (fun (z : E') => (fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) z) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) U z)) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) x)) v)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal extDerivFun_extDerivFun_chart"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop extDerivFun_extDerivFun_chart"
  logInfo "CURRENT_LITERAL_ELAB_OK:extDerivFun_extDerivFun_chart"

run_cmd liftTermElabM do
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [inst_5 : IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {X Y : (y : N) → TangentSpace.{u_5, 0, u_6, u_7} I' y} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (X y)) x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (Y y)) x → Eq.{1} ((mvfderiv I' f x) (VectorField.mlieBracket.{0, u_6, u_5, u_7} I' X Y x)) (HSub.hSub.{0, 0, 0} ((mvfderiv I' (fun (y : N) => (mvfderiv I' f y) (Y y)) x) (X x)) ((mvfderiv I' (fun (y : N) => (mvfderiv I' f y) (X y)) x) (Y x)))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen literal extDerivFun_apply_mlieBracket"
  unless ← isProp expected do
    throwError "expected frozen literal is not Prop extDerivFun_apply_mlieBracket"
  logInfo "CURRENT_LITERAL_ELAB_OK:extDerivFun_apply_mlieBracket"

