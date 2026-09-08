#!/bin/sh
# Dispatch one task to a codex worker in an isolated worktree (non-destructive).
# Usage: harness/dispatch_codex.sh <task_id> [prompt_file]
#   prompt_file defaults to harness/tasks/<task_id>.md; the worker contract is
#   expected to be part of that file. The worktree is
#   /private/tmp/poincare-workers/<task_id> on branch worker/<task_id> from main,
#   with an APFS-cloned .lake cache; an existing worktree is reused, never removed.
#   The codex model comes from ~/.codex/config.toml; reasoning effort is xhigh.
#   Output goes to harness/logs/<task_id>.log. Accept with harness/gate.sh.
set -eu
REPO=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
TASK=$1
PROMPT=${2:-$REPO/harness/tasks/$TASK.md}
WT=/private/tmp/poincare-workers/$TASK
[ -f "$PROMPT" ] || { echo "missing prompt file: $PROMPT" >&2; exit 2; }
mkdir -p /private/tmp/poincare-workers "$REPO/harness/logs"
if [ ! -d "$WT" ]; then
  git -C "$REPO" worktree add -q "$WT" -b "worker/$TASK" main
  cp -Rc "$REPO/.lake" "$WT/.lake"
fi
nohup codex exec -c model_reasoning_effort=xhigh --cd "$WT" --sandbox workspace-write \
  -c "sandbox_workspace_write.writable_roots=[\"$REPO/.git\"]" - < "$PROMPT" \
  > "$REPO/harness/logs/$TASK.log" 2>&1 &
echo "dispatched $TASK in $WT (pid $!); log harness/logs/$TASK.log"
