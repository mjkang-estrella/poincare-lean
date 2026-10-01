# Original flat-connection serialization evidence, helper a01

Original environment: clean HEAD `55e4859b54acb9044d7966a12df7a12afa8b52fd` in `/Users/mjkang/.codex/worktrees/incremental-verification/poincare`, Lean 4.30.0-rc2. No proof source, data definition, existing snapshot or existing probe was changed. All new evidence was created exclusively in this helper directory. No full build, helper agent, or 4.33 worker interaction occurred.

The a04 MDiff literal already succeeds when isolated: `isolated-mdiff-a01.result.json` records exit 0. The next serialized constant, `flatCovariantDerivative`, is the actual remaining failure: `isolated-flat-a01.result.json` records exit 1 with `ChartedSpace E (?m.66 𝕜 E)` stuck. Its result family was partially applied TangentSpace with no fixed base M.

`successful-mdiff-literal.json` records the successful complete literal and universe list `[u_1,u_2]`. `corrected-flat-literal.json` changes only the serialized tangent family from `(TangentSpace ... (modelWithCornersSelf ...))` to `(fun x : E => TangentSpace ... (modelWithCornersSelf ... ) x)`. This fixes the base type explicitly; it changes no hypothesis, norm dictionary, function or theorem.

`original-all14-corrected-a01.lean` is the unchanged original a04 rigid probe with that one quoted literal replaced. It retains every declaration, rigid universe arity, synthetic-metavariable rejection, `isDefEq`, and the original transitive permitted-axiom/unsafe/partial checks. `original-all14-corrected-a01.result.json` records exit 0. Its stdout contains all 14 `FROZEN_CONTRACT_OK` and all 14 `AXIOM_CONTRACT_OK` receipts. `corrected-literal-set-a01.json` supplies all 14 reviewed-input candidates for the root to serialize into a new snapshot.

This is original-environment literal serialization evidence, not a blind read-back or 4.33 proof acceptance. The original kernel type print is preserved separately; ellipses in that diagnostic print were never used as frozen literals. Root and the independent reviewer still own the corrected snapshot, review and migration gate.
