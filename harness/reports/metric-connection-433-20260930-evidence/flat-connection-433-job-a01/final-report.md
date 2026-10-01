# Flat connection migration Job a01

Worker gates passed; orchestrator acceptance is pending. Base is `37628ffa5cf60c2ab90994452279aaf1bc82dab4`; scoped result commit is `0d2e599a5a674fa8f7ca63c9c4b5f046c41b2d83` on `codex/flat-connection-433-a01`.

Only `Poincare/FlatModelConnection.lean` changed. The repair changes the Leibniz Prop-certificate and the approved bracket, curvature and Euclidean inner-compatibility proof bodies. Proof-local transparency handles the unchanged model tangent-space identifications. The Leibniz proof explicitly changes its scalar derivative term to `mfderiv` on the self models, applies `mfderiv_eq_fderiv`, then closes the canonical identification by reflexivity.

The computational map `toFun σ x := fderiv 𝕜 σ x`, its type and universe parameters, add certificate, smoothness instance, imports, all other proof bodies and source outside the four permitted bodies are byte-preserved by the sealed guard. All 14 original public types/universe lists and transitive permitted-axiom/unsafe/partial checks pass in the sealed a05 probe. No hypothesis, norm, topology dictionary, conditional package, import, definition or trust mechanism was added.

Evidence retains the failing baseline and five development source attempts. Each invocation directory records source, diff, argv, cwd, timestamps, stdout, stderr and exit. The remaining Leibniz goals narrowed from the model vector derivative to its canonical tangent identification, then to a reflexive equality; no outside-scope change was needed.

Final gates: `lean-a05` exit 0; `build-a01` exit 0 for the scoped target `Poincare.FlatModelConnection`; `frozen-probe-a01` exit 0 with 14 type and 14 axiom receipts; `scope-a05` exit 0; `diff-check-a01` exit 0; `token-scan-a01` exit 1 with empty output, meaning no forbidden-token matches. `gate-summary.json` records all results. Existing style/deprecation warnings remain in untouched source and existing CLM proof API use.

No full root build, root audits or completion audit was run. No original Hamilton, smoothability or core existence obligation is discharged. No merge, push or task acceptance occurred.

Exact first action for root: independently inspect the `37628ffa..0d2e599a5a674fa8f7ca63c9c4b5f046c41b2d83` scoped diff and rerun the six frozen Task commands from a suitable isolated review checkout with the original sealed context. Integrate only after independent acceptance; retain every old root import and the canonical final target.
