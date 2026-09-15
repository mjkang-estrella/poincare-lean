#!/bin/sh
# Dispatch one task to a codex worker in an isolated worktree (non-destructive).
# Usage: harness/dispatch_codex.sh <task_id> [prompt_file] [effort]
#   prompt_file defaults to harness/tasks/<task_id>.md; the worker contract is
#   expected to be part of that file. effort is the codex reasoning effort:
#   low for mechanical edits, medium for routine lemmas, high (default) for
#   frontier proofs; xhigh is not used (operator policy, 2026-09-07). The worktree is
#   /private/tmp/poincare-workers/<task_id> on branch worker/<task_id> from main,
#   with an APFS-cloned .lake cache; an existing worktree is reused, never removed.
#   The codex model comes from ~/.codex/config.toml (gpt-6-astra).
#   Output goes to harness/logs/<task_id>.log. Accept with harness/gate.sh.
set -eu
# 2026-09-15: the system git is the Xcode shim; point it at the Command Line Tools
# so workers never hit the license prompt.
if [ -d /Library/Developer/CommandLineTools ]; then
  export DEVELOPER_DIR=/Library/Developer/CommandLineTools
fi
REPO=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
TASK=$1
PROMPT=${2:-$REPO/harness/tasks/$TASK.md}
EFFORT=${3:-high}
case "$EFFORT" in low|medium|high) ;; *) echo "effort must be low, medium, or high" >&2; exit 2 ;; esac
WT=/private/tmp/poincare-workers/$TASK
[ -f "$PROMPT" ] || { echo "missing prompt file: $PROMPT" >&2; exit 2; }
mkdir -p /private/tmp/poincare-workers "$REPO/harness/logs"
if [ ! -d "$WT" ]; then
  git -C "$REPO" worktree add -q "$WT" -b "worker/$TASK" main
  cp -Rc "$REPO/.lake" "$WT/.lake"
fi
nohup codex exec -c "model_reasoning_effort=$EFFORT" --cd "$WT" --sandbox workspace-write \
  -c "sandbox_workspace_write.writable_roots=[\"$REPO/.git\"]" - < "$PROMPT" \
  > "$REPO/harness/logs/$TASK.log" 2>&1 &
echo "dispatched $TASK in $WT (pid $!); log harness/logs/$TASK.log"
