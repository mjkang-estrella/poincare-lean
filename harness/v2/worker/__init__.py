"""Bounded Leanstral fallback inference client for Harness v2.

This package deliberately has no patching, worktree, Git mutation, Lean, Ray,
or GPU control surface. Pi is the primary Job execution engine. This package
only runs fixed read-only Git safety checks, binds to one live Harness Job,
calls one pinned OpenAI-compatible model as an explicit fallback, and preserves
hash-bound evidence for Codex review.

The explicit-path ``snapshot.build_prompt_snapshot`` helper is intentionally
not exported here; it exists only for offline diagnostics and tests.
"""

from .binding import BindingError, JobBinding
from .client import (
    LeanstralConfig,
    LeanstralError,
    check_health,
    run_once,
    snapshot_job,
)
from .snapshot import SnapshotError

__all__ = [
    "BindingError",
    "JobBinding",
    "LeanstralConfig",
    "LeanstralError",
    "SnapshotError",
    "check_health",
    "run_once",
    "snapshot_job",
]
