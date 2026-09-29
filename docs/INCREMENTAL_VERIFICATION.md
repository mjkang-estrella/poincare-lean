# Verification during proof development

Verification has different costs at different stages. A development check can
reuse unchanged input state. Acceptance still requires an independent compiler
run against the exact candidate. Completion additionally requires the reserved
theorem, its allowed axiom footprint, a clean stable integration tree, and the
full completion audit at that tree.

| Stage | Check | Reuse boundary |
| --- | --- | --- |
| Status inspection | `sh scripts/read_status_summary.sh` | Previously recorded evidence bound to the source and toolchain; never completion certification. |
| Proof iteration | Scoped `lean_check` | Job-owned incremental document state; changed imports or dependency identity require a new session. |
| Independent review | `harness/v2/deploy/review-job-focused.sh` | Prebuilt base dependencies only; changed proof modules compile freshly. |
| Integration | Root build and audits | One serialized checkpoint for a compatible accepted batch. |
| Final completion | Exact declaration/type/axiom probe plus full audit | Fresh positive verification at the same clean stable HEAD. |

Use `lean_check` with `fresh: true` to request the full compiler during a job.
Explicit IO and metaprogramming commands use that path automatically. A clean
broker close also runs fresh scoped checks before sealing successful worker
evidence. Failed, revoked, expired, and blocked jobs cannot use incremental
diagnostics to bypass the final gate.

## Import direction

Local chart geometry and analytic carriers should import their specific
definitions and predecessor lemmas. They should not import Hamilton convergence
or sphere recognition merely to obtain those low-level definitions transitively.
Preserve existing theorem names and statements when trimming imports. Compare
declaration types and axiom footprints, compile the changed module, and check
its consumers before accepting an import change.

Keep proof files small at mathematical interfaces. Combining files increases
the amount re-elaborated when any part changes. Large final assembly and
historical route files belong at the integration end of the graph.

## Evidence and timing

The review runner combines required declaration checks into one compiler
invocation. Each frozen type remains checked and each declaration retains its
own evidence entry. The batch source and compiler transcript record the actual
shared execution. A missing declaration, a changed secondary type, an
unpermitted axiom, or any compiler failure rejects the entire batch.

Record cache validation, source snapshot setup, compilation, root overlay,
declaration probes, and audit durations separately. Import graph counts are
structural measurements, not compilation speedups. Compare timings on the same
host, toolchain, sources, and warm-cache conditions.

Status receipts preserve the timestamp and identity of the original check.
Changing source, dependencies, toolchain, verification code, gate policy, or
the saved status artifact invalidates reuse. A receipt does not upgrade an
incomplete or failed checkpoint into successful verification.

With `--reuse-negative`, the deployment's exact declaration probe may reuse only a compiler-confirmed
absence with unchanged source, toolchain, configuration, and actual compiled
import closure. Its output identifies the original negative evidence. Positive,
invalid, or nonstandard-axiom results are never reused. Pass `--fresh` to
`harness/v2/deploy/exact-completion-probe.sh` to force a new probe. Fresh probing
is the default, since validating a mutable cache can cost more than loading
the compiled environment. Explicit fresh checks omit import-manifest output.

## Integrity of reusable caches

Read-only permissions and a read-only worker mount do not prove that the host
cache is immutable. An ordinary cache therefore still receives full content
validation. Fast validation requires a positively verified protected generation
and exact manifest identity. Changes to that protection or identity invalidate
reuse. Worker-produced compiler outputs never become independent acceptance
evidence merely because a development check succeeded.

Linux Bubblewrap and systemd resource isolation remain the production worker
boundary. A direct local language-server smoke test exercises Lean's protocol;
it does not establish that Linux deployment isolation works on this host.

## Local measurement on 2026-09-29

On the Mac's pinned Lean 4.30.0-rc2, the actual buffered solver document took
61.047 seconds for the initial language-server check. Appending a `#check` of
its existing parametrix theorem took 0.721 seconds in the same process; repeating
identical input reused the success in 0.000101 seconds. Fresh compilation of
the entire file took 59.31 seconds. This measures an appended declaration
check after a retained proof prefix, not an arbitrary proof edit or Linux
deployment. Raw diagnostics, timings, and bounded transport counters are in
the ignored `harness/v2/state/incremental-verification/session-benchmark-transport-fixed`.

The import-only reduction changed solver predecessors from 641 to 196 and
tensor-carrier predecessors from 630 to 110. Warm full-file checks stayed
about the same, so no compilation speedup is attributed to those counts.

The integration build reported 4,202 dependency/artifact jobs, but its log had
only seven freshly built targets. It completed in 38.547 seconds. Job count is
not a measure of how many proofs were re-elaborated.
