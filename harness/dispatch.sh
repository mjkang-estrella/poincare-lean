#!/bin/bash
# Dispatch a ledger task to a codex worker in an isolated worktree.
# Usage: dispatch.sh <task_id> <prompt_file>
# Creates worktree at ../poincare-wt-<task_id>, clones .lake via APFS clonefile,
# runs codex exec (gpt-5.5, xhigh) inside it. Logs to harness/logs/<task_id>.log.
set -euo pipefail
REPO=/Users/mjkang/Develop/poincare
TASK="$1"; PROMPT_FILE="$2"
WT="$REPO/../poincare-wt-$TASK"
BRANCH="worker/$TASK"

cd "$REPO"
git worktree remove --force "$WT" 2>/dev/null || true
git branch -D "$BRANCH" 2>/dev/null || true
git worktree add -b "$BRANCH" "$WT" HEAD
# APFS copy-on-write clone of the build cache (~instant, no real disk until divergence)
cp -Rc "$REPO/.lake" "$WT/.lake"

codex exec \
  -m gpt-5.5 \
  -c model_reasoning_effort=xhigh \
  --cd "$WT" \
  --sandbox workspace-write \
  - < "$PROMPT_FILE" \
  > "$REPO/harness/logs/$TASK.log" 2>&1
echo "worker $TASK finished; log: harness/logs/$TASK.log"
