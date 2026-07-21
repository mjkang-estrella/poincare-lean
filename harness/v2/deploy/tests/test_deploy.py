from __future__ import annotations

import json
import os
import shutil
import sqlite3
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
COMMON = ROOT / "harness/v2/deploy/common.sh"
RUN_JOB_SUPERVISED = ROOT / "harness/v2/deploy/run-job-supervised.sh"
STOP = ROOT / "harness/v2/deploy/stop.sh"
GIT_EXECUTABLE = Path(shutil.which("git") or "/usr/bin/git").resolve()
TMUX_TEST_EXECUTABLE = Path(shutil.which("true") or "/usr/bin/true").resolve()
AUTHORITY_SCRIPTS = tuple(
    ROOT / "harness/v2/deploy" / name
    for name in (
        "run-job-supervised.sh",
        "launch.sh",
        "stop.sh",
        "status.sh",
        "codex-cycle.sh",
        "worker-plane.sh",
        "heartbeat-loop.sh",
        "evidence-heartbeat.sh",
        "exact-completion-probe.sh",
    )
)


def run_bash(script: str, *arguments: str, check: bool = False) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["bash", "-c", script, "bash", str(COMMON), *arguments],
        check=check,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def write_sealed_pi_inputs(root: Path) -> tuple[Path, Path]:
    install_manifest = root / "pi-install.json"
    dependency_graph = root / "npm-ls.json"
    for path in (install_manifest, dependency_graph):
        if not path.exists():
            path.write_text("{}\n", encoding="utf-8")
        path.chmod(0o400)
    return install_manifest, dependency_graph


def write_config(
    path: Path,
    root: Path,
    *,
    timeout: int | None = None,
    branch: bool = True,
    maximum_jobs: int | None = None,
    backlog_target: int | None = None,
) -> None:
    install_manifest, dependency_graph = write_sealed_pi_inputs(root)
    values = [
        f"POINCARE_REPO_ROOT={root / 'repo'}",
        f"POINCARE_WORKTREE_ROOT={root / 'worktrees'}",
        "POINCARE_CODEX_BIN=/bin/true",
        f"POINCARE_GIT_BIN={GIT_EXECUTABLE}",
        f"POINCARE_TMUX_BIN={TMUX_TEST_EXECUTABLE}",
        f"POINCARE_PI_INSTALL_MANIFEST={install_manifest}",
        f"POINCARE_PI_DEPENDENCY_GRAPH={dependency_graph}",
        f"POINCARE_PI_LAKE_CACHE_ROOT={root / 'cache'}",
        f"POINCARE_PI_TOOLCHAIN_ROOT={root / 'toolchain'}",
        f"POINCARE_EXTRA_PATH={Path(sys.executable).parent}:/usr/local/bin:/usr/bin:/bin",
        "POINCARE_LEANSTRAL_BASE_URL=http://127.0.0.1:9999/v1",
        "POINCARE_LEANSTRAL_SERVED_MODEL=leanstral-test",
        "POINCARE_LEANSTRAL_ARTIFACT=mistralai/Leanstral-1.5-119B-A6B",
        f"POINCARE_LEANSTRAL_REVISION={'a' * 40}",
    ]
    if branch:
        values.append("POINCARE_INTEGRATION_BRANCH=main")
    if timeout is not None:
        values.append(f"POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS={timeout}")
    if maximum_jobs is not None:
        values.append(f"POINCARE_MAX_LEANSTRAL_JOBS={maximum_jobs}")
    if backlog_target is not None:
        values.append(f"POINCARE_LEANSTRAL_BACKLOG_TARGET={backlog_target}")
    path.write_text("\n".join(values) + "\n", encoding="utf-8")
    path.chmod(0o600)


class CachePublisherArgumentTest(unittest.TestCase):
    def test_flock_reexec_preserves_source_and_mandatory_provenance(self) -> None:
        script = r'''
source "$1"
cache_publish_reexec_args "/srv/projects/poincare base" "/tmp/cache evidence/provenance.json" "/tmp/harness env"
printf '<%s>\n' "${POINCARE_CACHE_PUBLISH_REEXEC_ARGS[@]}"
'''
        result = subprocess.run(
            ["bash", "-c", script, "bash", str(COMMON)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        self.assertEqual(
            result.stdout.splitlines(),
            [
                "<--source-root>",
                "</srv/projects/poincare base>",
                "<--provenance>",
                "</tmp/cache evidence/provenance.json>",
                "</tmp/harness env>",
            ],
        )


class JobUtilizationSnapshotTest(unittest.TestCase):
    def test_reviewing_jobs_do_not_hide_execution_underfill(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state = Path(temporary).resolve()
            database = state / "harness.sqlite3"
            connection = sqlite3.connect(database)
            connection.execute("CREATE TABLE jobs(state TEXT NOT NULL)")
            connection.executemany(
                "INSERT INTO jobs(state) VALUES (?)",
                [("queued",), ("running",), ("reviewing",), ("reviewing",)],
            )
            connection.commit()
            connection.close()
            result = run_bash(
                'source "$1"; POINCARE_STATE_DIR=$2; '
                'export POINCARE_MAX_LEANSTRAL_JOBS=4 '
                'POINCARE_LEANSTRAL_BACKLOG_TARGET=4; job_utilization_snapshot',
                str(state),
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            payload = json.loads(result.stdout)
            self.assertEqual(payload["queued"], 1)
            self.assertEqual(payload["executing"], 1)
            self.assertEqual(payload["reviewing"], 2)
            self.assertEqual(payload["execution_backlog"], 2)
            self.assertEqual(payload["target"], 4)
            self.assertEqual(payload["underfilled"], 2)


class RunJobSupervisorArgumentTest(unittest.TestCase):
    def test_job_argv_uses_sealed_pi_attestations_and_never_pi_bin(self) -> None:
        source = RUN_JOB_SUPERVISED.read_text(encoding="utf-8")
        marker = "job_argv=(\n"
        self.assertIn(marker, source)
        job_argv = source.split(marker, 1)[1].split("\n)\n", 1)[0]
        self.assertEqual(
            job_argv.count('--pi-install-manifest "$POINCARE_PI_INSTALL_MANIFEST"'),
            1,
        )
        self.assertEqual(
            job_argv.count('--pi-dependency-graph "$POINCARE_PI_DEPENDENCY_GRAPH"'),
            1,
        )
        self.assertNotIn("--pi-bin", source)
        self.assertNotIn("POINCARE_PI_BIN", source)
        self.assertNotIn("supervisor-pycache", source)
        self.assertNotIn("PYTHONPYCACHEPREFIX", source)
        self.assertIn('row["state"] != "running"', source)
        self.assertIn('float(row["lease_expires_at"]) <= time.time()', source)
        self.assertEqual(
            source.count('HARNESS_PI_SYSTEMD_RUN="$HARNESS_PI_SYSTEMD_RUN"'),
            1,
        )
        self.assertEqual(source.count('HARNESS_PI_GIT="$HARNESS_PI_GIT"'), 1)

    def test_execution_and_capacity_locks_cover_the_entire_broker_lifetime(self) -> None:
        source = RUN_JOB_SUPERVISED.read_text(encoding="utf-8")
        lifecycle = source.index('exec 8> "$POINCARE_DEPLOY_STATE_DIR/lifecycle.lock"')
        execution = source.index('exec {job_execution_fd}<> "$execution_lock"')
        capacity = source.index('for (( candidate_slot=1;')
        admission = source.index('artifact_dir=$(')
        child = source.index('"${job_argv[@]}" 8>&- &')
        wait = source.index('wait "$child_pid"')
        self.assertLess(lifecycle, execution)
        self.assertLess(capacity, execution)
        self.assertLess(capacity, admission)
        self.assertLess(execution, admission)
        self.assertLess(admission, child)
        self.assertLess(child, wait)
        self.assertIn('"$HARNESS_PI_FLOCK" --nonblock "$job_execution_fd"', source)
        self.assertIn('"$HARNESS_PI_FLOCK" --nonblock "$candidate_slot_fd"', source)
        self.assertIn('"capacity_slot": int(capacity_slot)', source)
        self.assertIn('candidate_slot<=4', source)
        self.assertIn('occupied_slots >= POINCARE_MAX_LEANSTRAL_JOBS', source)
        self.assertIn('"${job_argv[@]}" 8>&- &', source)
        release_execution = source.rindex('exec {job_execution_fd}>&-')
        release_capacity = source.rindex('exec {capacity_slot_fd}>&-')
        review = source.index('--state reviewing >/dev/null')
        self.assertGreater(release_execution, wait)
        self.assertGreater(release_capacity, wait)
        self.assertLess(release_execution, review)
        self.assertLess(release_capacity, review)

    def test_automatic_dispatch_renews_and_routes_pi_results(self) -> None:
        source = RUN_JOB_SUPERVISED.read_text(encoding="utf-8")
        self.assertIn("--dispatch-next", source)
        self.assertIn("runtime_cli job claim", source)
        self.assertIn("--queued-only", source)
        self.assertIn("readonly job_lease_seconds=900", source)
        self.assertIn("readonly job_heartbeat_seconds=60", source)
        self.assertIn("job_feedback_passed_to_review", source)
        self.assertIn("job_feedback_blocked", source)
        self.assertIn("job_feedback_retry_required", source)
        self.assertIn("immutable_retry true", source)
        self.assertIn("pi_execution_unsuccessful", source)
        self.assertNotIn("runtime_cli job review", source)
        self.assertNotIn("runtime_cli task transition", source)

    def test_supervisor_record_is_atomically_published_after_traps_exist(self) -> None:
        source = RUN_JOB_SUPERVISED.read_text(encoding="utf-8")
        trap_index = source.index("trap finalize_supervisor EXIT")
        staging_index = source.index('staging_dir="$staging_root/')
        rename_index = source.index("os.rename(staging_directory, final_directory)")
        child_index = source.index('"${job_argv[@]}" 8>&- &')
        self.assertLess(trap_index, staging_index)
        self.assertLess(staging_index, rename_index)
        self.assertLess(rename_index, child_index)
        self.assertIn('workers/staging', source)
        self.assertIn("create a fresh immutable Job", source)


class DeploymentAuthorityTest(unittest.TestCase):
    def test_worker_plane_fills_execution_slots_without_acceptance_authority(self) -> None:
        source = (ROOT / "harness/v2/deploy/worker-plane.sh").read_text(
            encoding="utf-8"
        )
        self.assertIn("queued_job_count", source)
        self.assertIn("job_supervisor_report", source)
        self.assertIn('"$SCRIPT_DIR/run-job-supervised.sh" --dispatch-next', source)
        self.assertIn("POINCARE_MAX_LEANSTRAL_JOBS - occupied", source)
        self.assertNotIn("runtime_cli job review", source)
        self.assertNotIn("runtime_cli task transition", source)
        self.assertNotIn("git commit", source)

    def test_codex_host_authority_does_not_use_a_uid_remapping_sandbox(self) -> None:
        source = (ROOT / "harness/v2/deploy/codex-cycle.sh").read_text(
            encoding="utf-8"
        )
        self.assertIn("--sandbox danger-full-access", source)
        self.assertNotIn("--sandbox workspace-write", source)
        self.assertNotIn("sandbox_workspace_write.writable_roots", source)

    def test_codex_prioritizes_a_measured_bounded_execution_backlog(self) -> None:
        cycle = (ROOT / "harness/v2/deploy/codex-cycle.sh").read_text(
            encoding="utf-8"
        )
        prompt = (ROOT / "harness/v2/prompts/orchestrator.md").read_text(
            encoding="utf-8"
        )
        status = (ROOT / "harness/v2/deploy/status.sh").read_text(encoding="utf-8")
        heartbeat = (ROOT / "harness/v2/deploy/evidence-heartbeat.sh").read_text(
            encoding="utf-8"
        )
        schema = json.loads(
            (ROOT / "harness/v2/prompts/cycle-result.schema.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertIn("job_utilization_snapshot", cycle)
        self.assertIn("Configured execution-backlog target", cycle)
        self.assertIn("replenish", cycle)
        self.assertIn("Keep inference fed while Codex reviews", prompt)
        self.assertIn("Replenishment has priority", prompt)
        self.assertIn("compatible accepted commits", prompt)
        self.assertIn("job_utilization_snapshot", status)
        self.assertIn('counts["underfilled"]', status)
        self.assertIn("job_utilization_snapshot", heartbeat)
        self.assertIn("backlog_underfilled", heartbeat)
        self.assertIn("execution_backlog", schema["required"])
        self.assertIn("underfill_reason", schema["properties"]["execution_backlog"]["required"])
        self.assertIn('underfilled != max(0, target - sum(counts))', cycle)

    def test_linux_authority_paths_are_absolute_and_remaining_scripts_use_them(self) -> None:
        common = COMMON.read_text(encoding="utf-8")
        self.assertIn("readonly HARNESS_PI_PYTHON=/usr/bin/python3", common)
        self.assertIn("readonly HARNESS_PI_FLOCK=/usr/bin/flock", common)
        self.assertIn('"$HARNESS_PI_TMUX" "$@"', common)
        self.assertIn('HARNESS_PI_GIT_SHA256="$HARNESS_PI_GIT_SHA256"', common)
        for path in AUTHORITY_SCRIPTS:
            source = path.read_text(encoding="utf-8")
            self.assertNotIn("require_command flock", source, path.name)
            self.assertNotIn("require_command git", source, path.name)
            self.assertNotIn("require_command setsid", source, path.name)
            self.assertNotIn("require_command timeout", source, path.name)
            self.assertNotIn("exec flock ", source, path.name)
            self.assertNotIn("| python3 ", source, path.name)
            self.assertNotIn("$(python3 ", source, path.name)
            self.assertNotIn("$(git -C", source, path.name)
            self.assertNotIn("\ngit -C", source, path.name)
            self.assertNotIn("\nenv -i", source, path.name)
            self.assertNotIn("\nsetsid --", source, path.name)
        self.assertIn("/usr/bin/env -i", common)
        self.assertNotIn("\n    env -i", common)

    def test_completion_audit_uses_the_pinned_toolchain_and_records_exact_argv(self) -> None:
        source = (ROOT / "harness/v2/deploy/codex-cycle.sh").read_text(
            encoding="utf-8"
        )
        self.assertIn(
            '"PATH=$POINCARE_PI_TOOLCHAIN_ROOT/bin:/usr/bin:/bin"', source
        )
        self.assertIn("/bin/sh scripts/completion_audit.sh", source)
        self.assertIn('f"PATH={toolchain_root}/bin:/usr/bin:/bin"', source)
        self.assertIn('"/bin/sh",\n            "scripts/completion_audit.sh"', source)
        self.assertNotIn("env LEAN_NUM_THREADS=1 sh scripts/completion_audit.sh", source)

    def test_preflight_requires_and_records_the_exact_attested_node_runtime(self) -> None:
        source = (ROOT / "harness/v2/deploy/preflight.sh").read_text(
            encoding="utf-8"
        )
        self.assertIn('manifest["node"]["path"] != "/usr/bin/node"', source)
        self.assertIn('expected_node_executable="/usr/bin/node"', source)
        self.assertIn('"minimum_version": manifest["node"]["minimum_version"]', source)
        self.assertIn('"version": manifest["node"]["version"]', source)
        self.assertIn('json.load(sys.stdin)["node"]["version"]', source)
        self.assertIn(
            'PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1', source
        )
        self.assertIn(
            "--unshare-all --unshare-user --disable-userns", source
        )
        self.assertGreaterEqual(
            source.count('PYTHONPATH="$POINCARE_REPO_ROOT" PYTHONNOUSERSITE=1'),
            5,
        )
        self.assertNotIn("command -v node", source)

    def test_stop_fences_dispatch_before_reaping_and_releases_scopes_after_reap(self) -> None:
        source = STOP.read_text(encoding="utf-8")
        durable_stop = source.index("set_deployment_desired_state stopped")
        audit = source.index("supervisor_report=$(job_supervisor_report)")
        signal = source.index("signal_recorded_supervisor_group")
        terminalize = source.index('runtime_cli job interrupt-stopped "$job_id"')
        tmux_kill = source.index('tmux kill-session -t "$session_id"')
        self.assertLess(durable_stop, audit)
        self.assertLess(audit, signal)
        self.assertLess(signal, terminalize)
        self.assertLess(terminalize, tmux_kill)
        self.assertNotIn("runtime_cli job finish", source)
        self.assertNotIn("runtime_cli job claim", source)
        self.assertIn('item["live"] or item["group_members"]', source)
        self.assertIn('"orphaned_supervisor_process_group"', source)
        self.assertIn('"exited_supervisor_still_live"', source)
        self.assertIn('for record in report["records"]:', source)
        self.assertIn('record["live"] or record["group_members"]', source)

    def test_lock_markers_are_not_authority_and_failed_launch_rolls_back(self) -> None:
        launch = (ROOT / "harness/v2/deploy/launch.sh").read_text(encoding="utf-8")
        for path in AUTHORITY_SCRIPTS:
            source = path.read_text(encoding="utf-8")
            self.assertNotIn('${POINCARE_LIFECYCLE_LOCKED:-0}', source, path.name)
            self.assertNotIn('${POINCARE_CONTROL_LOCKED:-0}', source, path.name)
            self.assertNotIn('${POINCARE_WORKERS_LOCKED:-0}', source, path.name)
            self.assertNotIn('${POINCARE_OBSERVE_LOCKED:-0}', source, path.name)
        self.assertIn('"$HARNESS_PI_FLOCK" --nonblock 7', launch)
        self.assertIn("rollback_failed_launch", launch)
        self.assertIn("deploy-launch-rollback", launch)
        self.assertLess(
            launch.index('[[ "$(active_job_count)" == 0 ]]'),
            launch.index("set_deployment_desired_state running"),
        )


class RuntimeLayoutTest(unittest.TestCase):
    def test_runtime_layout_is_created_without_following_state_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            repo = root / "repo"
            (repo / "harness/v2").mkdir(parents=True)
            state = repo / "harness/v2/state"
            valid = run_bash(
                'source "$1"; POINCARE_REPO_ROOT=$2; POINCARE_STATE_DIR=$2/harness/v2/state; '
                'POINCARE_DEPLOY_STATE_DIR=$POINCARE_STATE_DIR/deploy; ensure_runtime_layout',
                str(repo),
            )
            self.assertEqual(valid.returncode, 0, valid.stderr)
            self.assertTrue((state / "deploy/workers/supervisors").is_dir())
            self.assertTrue((state / "deploy/workers/staging").is_dir())
            self.assertTrue((state / "deploy/observe/snapshots").is_dir())
            self.assertTrue((state / "execution-locks").is_dir())
            expected_locks = (
                state / "deploy/lifecycle.lock",
                state / "deploy/control/codex-cycle.lock",
                state / "deploy/workers/worker-plane.lock",
                state / "deploy/observe/heartbeat-loop.lock",
                *(state / f"deploy/workers/slots/slot-{slot}.lock" for slot in range(1, 5)),
            )
            for lock in expected_locks:
                metadata = lock.stat(follow_symlinks=False)
                self.assertTrue(stat.S_ISREG(metadata.st_mode), lock)
                self.assertEqual(stat.S_IMODE(metadata.st_mode), 0o600, lock)
                self.assertEqual(metadata.st_nlink, 1, lock)

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            repo = root / "repo"
            outside = root / "outside"
            (repo / "harness/v2").mkdir(parents=True)
            outside.mkdir()
            (repo / "harness/v2/state").symlink_to(outside, target_is_directory=True)
            rejected = run_bash(
                'source "$1"; POINCARE_REPO_ROOT=$2; POINCARE_STATE_DIR=$2/harness/v2/state; '
                'POINCARE_DEPLOY_STATE_DIR=$POINCARE_STATE_DIR/deploy; ensure_runtime_layout',
                str(repo),
            )
            self.assertNotEqual(rejected.returncode, 0)
            self.assertFalse((outside / "deploy").exists())


class SecureConfigurationTest(unittest.TestCase):
    def test_insecure_config_is_rejected_before_sourcing(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            config = root / "deploy.env"
            sentinel = root / "sourced"
            config.write_text(f"touch {sentinel}\n", encoding="utf-8")
            config.chmod(0o644)
            result = run_bash('source "$1"; load_config "$2"', str(config))
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(sentinel.exists())
            self.assertIn("0400 or 0600 before sourcing", result.stderr)

    def test_symlink_and_noncanonical_config_paths_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            config = root / "deploy.env"
            write_config(config, root)
            symlink = root / "linked.env"
            symlink.symlink_to(config)
            linked = run_bash('source "$1"; load_config "$2"', str(symlink))
            self.assertNotEqual(linked.returncode, 0)
            noncanonical = run_bash(
                'source "$1"; load_config "$2"',
                str(root / "." / "deploy.env") + "/../deploy.env",
            )
            self.assertNotEqual(noncanonical.returncode, 0)

    def test_cycle_budget_defaults_to_four_hours_and_rejects_less(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            config = root / "deploy.env"
            write_config(config, root)
            result = run_bash(
                'source "$1"; load_config "$2"; printf "%s\\n" "$POINCARE_CODEX_CYCLE_TIMEOUT_SECONDS"',
                str(config),
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), "14400")
            write_config(config, root, timeout=14399)
            too_short = run_bash('source "$1"; load_config "$2"', str(config))
            self.assertNotEqual(too_short.returncode, 0)
            self.assertIn("between 14400 and 86400", too_short.stderr)

    def test_integration_branch_must_be_in_the_config_file(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            config = root / "deploy.env"
            write_config(config, root, branch=False)
            result = run_bash(
                'source "$1"; export POINCARE_INTEGRATION_BRANCH=ambient; load_config "$2"',
                str(config),
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("POINCARE_INTEGRATION_BRANCH", result.stderr)

    def test_backlog_target_defaults_to_ceiling_and_cannot_exceed_it(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            config = root / "deploy.env"
            write_config(config, root, maximum_jobs=3)
            defaulted = run_bash(
                'source "$1"; load_config "$2"; printf "%s/%s\\n" '
                '"$POINCARE_LEANSTRAL_BACKLOG_TARGET" "$POINCARE_MAX_LEANSTRAL_JOBS"',
                str(config),
            )
            self.assertEqual(defaulted.returncode, 0, defaulted.stderr)
            self.assertEqual(defaulted.stdout.strip(), "3/3")

            write_config(config, root, maximum_jobs=2, backlog_target=3)
            rejected = run_bash('source "$1"; load_config "$2"', str(config))
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn("POINCARE_LEANSTRAL_BACKLOG_TARGET", rejected.stderr)
            self.assertIn("between 1 and 2", rejected.stderr)


class TrustBoundaryTest(unittest.TestCase):
    def make_control_repo(self, root: Path) -> Path:
        repo = root / "control"
        for relative in (
            "harness/v2/runtime",
            "harness/v2/pi",
            "harness/v2/worker",
            "harness/v2/schemas",
            "harness/v2/deploy",
            "harness/v2/prompts",
        ):
            (repo / relative).mkdir(parents=True, exist_ok=True)
            (repo / relative / "tracked.txt").write_text(relative + "\n", encoding="utf-8")
        for relative in (
            "AGENTS.md",
            "harness/__init__.py",
            "harness/v2/__init__.py",
            "harness/v2/SPEC.md",
            "harness/v2/RUNBOOK.md",
        ):
            path = repo / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(relative + "\n", encoding="utf-8")
        subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True)
        subprocess.run(["git", "-C", str(repo), "config", "user.name", "Test"], check=True)
        subprocess.run(["git", "-C", str(repo), "config", "user.email", "test@example.invalid"], check=True)
        subprocess.run(["git", "-C", str(repo), "add", "."], check=True)
        subprocess.run(["git", "-C", str(repo), "commit", "-qm", "control"], check=True)
        return repo

    def manifest(self, repo: Path) -> subprocess.CompletedProcess[str]:
        return run_bash(
            'source "$1"; POINCARE_REPO_ROOT=$2; control_surface_manifest',
            str(repo),
        )

    def test_manifest_requires_tracked_clean_head_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = self.make_control_repo(Path(temporary).resolve())
            clean = self.manifest(repo)
            self.assertEqual(clean.returncode, 0, clean.stderr)
            payload = json.loads(clean.stdout)
            self.assertEqual(payload["schema_version"], "poincare.deploy-control-surface.v1")
            target = repo / "harness/v2/deploy/tracked.txt"
            target.write_text("tampered\n", encoding="utf-8")
            dirty = self.manifest(repo)
            self.assertNotEqual(dirty.returncode, 0)
            subprocess.run(["git", "-C", str(repo), "restore", str(target)], check=True)
            (repo / "harness/v2/deploy/untracked.sh").write_text("exit 0\n", encoding="utf-8")
            untracked = self.manifest(repo)
            self.assertNotEqual(untracked.returncode, 0)

    def test_manifest_rejects_symlink_in_control_surface(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = self.make_control_repo(Path(temporary).resolve())
            (repo / "harness/v2/deploy/redirected").symlink_to("tracked.txt")
            result = self.manifest(repo)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("symlink", result.stderr)


class LifecycleAndCadenceTest(unittest.TestCase):
    def test_tmux_authority_ignores_a_path_shadow(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            shadow = root / "shadow"
            shadow.mkdir()
            sentinel = root / "ambient-tmux-used"
            ambient_tmux = shadow / "tmux"
            ambient_tmux.write_text(
                f"#!/bin/sh\ntouch '{sentinel}'\nexit 99\n", encoding="utf-8"
            )
            ambient_tmux.chmod(0o755)
            script = r'''
source "$1"
HARNESS_PI_TMUX=$2
payload=$(secure_executable_payload "$HARNESS_PI_TMUX")
HARNESS_PI_TMUX_SHA256=$(printf '%s' "$payload" | "$HARNESS_PI_PYTHON" -S -P -B -c \
  'import json,sys; print(json.load(sys.stdin)["sha256"])')
PATH=$3
tmux --version
'''
            result = run_bash(
                script, str(TMUX_TEST_EXECUTABLE), str(shadow)
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(sentinel.exists())

    def test_authenticated_bootstrap_is_finalized_without_duplicate_respawn(self) -> None:
        script = r'''
source "$1"
POINCARE_CONFIG_FILE=/tmp/deploy.env
POINCARE_SESSION_OWNER=owner-fingerprint
FAKE_STATE=bootstrap
FAKE_START="/control/worker-plane.sh /tmp/deploy.env"
TMUX_LOG=$2
session_is_owned() { return 1; }
session_is_bootstrap_owned() { return 0; }
session_id_exact() { printf '@9\n'; }
session_id_is_live_owned() { return 0; }
tmux() {
  case "$1" in
    list-sessions) printf 'poincare-workers|@9\n' ;;
    show-options)
      case "${*: -1}" in
        @poincare_harness_owner) printf 'owner-fingerprint\n' ;;
        @poincare_harness_role) printf 'workers\n' ;;
        @poincare_harness_base_pane) printf '%%4\n' ;;
        @poincare_harness_state) printf '%s\n' "$FAKE_STATE" ;;
      esac
      ;;
    display-message)
      case "${*: -1}" in
        '#{session_name}') printf 'poincare-workers\n' ;;
        '#{session_id}') printf '@9\n' ;;
        '#{pane_start_command}') printf '%s\n' "$FAKE_START" ;;
        '#{pane_dead}') printf '0\n' ;;
      esac
      ;;
    set-option)
      if [[ "${*: -2:1}" == @poincare_harness_state ]]; then
        FAKE_STATE=${*: -1}
        printf 'state=%s\n' "$FAKE_STATE" >> "$TMUX_LOG"
      fi
      ;;
    respawn-pane) printf 'RESPAWN\n' >> "$TMUX_LOG" ;;
    set-window-option) : ;;
    *) return 1 ;;
  esac
}
start_or_recover_session poincare-workers sentinel /control/worker-plane.sh
cat "$TMUX_LOG"
'''
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / "tmux.log"
            result = run_bash(script, str(log))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("state=running", result.stdout)
            self.assertNotIn("RESPAWN", result.stdout)

    def test_heartbeat_deadline_is_start_anchored_and_records_overrun(self) -> None:
        result = run_bash(
            'source "$1"; heartbeat_timing_metrics 100 250 120',
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["deadline_monotonic_ns"], 220)
        self.assertEqual(payload["duration_ns"], 150)
        self.assertEqual(payload["overrun_ns"], 30)
        self.assertEqual(payload["remaining_ns"], 0)


class SupervisorAuditTest(unittest.TestCase):
    def make_fixture(self, root: Path, *, recorded_start: int = 456) -> tuple[Path, Path, str]:
        state = root / "state"
        supervisors = state / "deploy/workers/supervisors/job-001"
        supervisors.mkdir(parents=True, mode=0o700)
        supervisors.parent.chmod(0o700)
        proc = root / "proc"
        (proc / "sys/kernel/random").mkdir(parents=True)
        boot_id = "12345678-1234-1234-1234-123456789abc"
        (proc / "sys/kernel/random/boot_id").write_text(boot_id + "\n", encoding="ascii")
        (proc / "123").mkdir()
        fields = "S 1 123 123 0 -1 0 0 0 0 0 0 0 0 0 0 0 1 0 456"
        (proc / "123/stat").write_text(f"123 (supervisor) {fields}\n", encoding="utf-8")
        database = state / "harness.sqlite3"
        connection = sqlite3.connect(database)
        connection.execute(
            "CREATE TABLE jobs(job_id TEXT, state TEXT, lease_owner TEXT, lease_generation INTEGER, lease_expires_at REAL)"
        )
        connection.execute(
            "INSERT INTO jobs VALUES(?,?,?,?,?)",
            ("job-001", "running", "owner", 7, time.time() + 600),
        )
        connection.commit()
        connection.close()
        launch = {
            "schema_version": "poincare.job-supervisor.v2",
            "job_id": "job-001",
            "lease_owner": "owner",
            "lease_token": 7,
            "supervisor_pid": 123,
            "supervisor_start_ticks": recorded_start,
            "process_group_id": 123,
            "session_id": 123,
            "boot_id": boot_id,
            "config_fingerprint": "fingerprint",
            "started_at": "2026-07-19T00:00:00Z",
            "argv": ["/usr/bin/python3", "-m", "harness.v2.pi"],
            "cwd": "/srv/projects/poincare",
            "capacity_slot": 1,
        }
        launch_path = supervisors / "launch.json"
        launch_path.write_text(json.dumps(launch) + "\n", encoding="utf-8")
        launch_path.chmod(0o400)
        return state, proc, boot_id

    def audit(self, state: Path, proc: Path) -> subprocess.CompletedProcess[str]:
        return run_bash(
            'source "$1"; POINCARE_STATE_DIR=$2; POINCARE_DEPLOY_STATE_DIR=$2/deploy; '
            'POINCARE_CONFIG_FINGERPRINT=fingerprint; job_supervisor_report "$3"',
            str(state),
            str(proc),
        )

    def test_live_supervisor_requires_exact_pid_start_time_and_pgid(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state, proc, _ = self.make_fixture(Path(temporary).resolve())
            healthy = self.audit(state, proc)
            self.assertEqual(healthy.returncode, 0, healthy.stderr)
            self.assertEqual(json.loads(healthy.stdout)["live_supervisors"], 1)

        with tempfile.TemporaryDirectory() as temporary:
            state, proc, _ = self.make_fixture(Path(temporary).resolve(), recorded_start=999)
            stale = self.audit(state, proc)
            self.assertEqual(stale.returncode, 2)
            codes = {item["code"] for item in json.loads(stale.stdout)["anomalies"]}
            self.assertIn("supervisor_missing_exit", codes)
            self.assertIn("active_job_supervisor_not_live", codes)

    def test_exit_record_does_not_hide_a_live_recorded_process_group(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state, proc, _ = self.make_fixture(Path(temporary).resolve())
            exit_path = state / "deploy/workers/supervisors/job-001/exit.json"
            exit_path.write_text(
                json.dumps(
                    {
                        "schema_version": "poincare.job-supervisor-exit.v1",
                        "job_id": "job-001",
                        "finished_at": "2026-07-19T00:01:00Z",
                        "outcome": "exited",
                        "exit_code": 0,
                        "recorded_by": "test",
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            exit_path.chmod(0o400)
            report = self.audit(state, proc)
            self.assertEqual(report.returncode, 2)
            payload = json.loads(report.stdout)
            codes = {item["code"] for item in payload["anomalies"]}
            self.assertIn("exited_supervisor_still_live", codes)
            record = payload["records"][0]
            self.assertTrue(record["exit_recorded"])
            self.assertFalse(record["live"])
            self.assertEqual(record["group_members"], [123])

    def test_completed_review_supervisor_does_not_block_queued_dispatch_audit(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state, proc, _ = self.make_fixture(Path(temporary).resolve())
            connection = sqlite3.connect(state / "harness.sqlite3")
            connection.execute("UPDATE jobs SET state = 'reviewing'")
            connection.execute(
                "INSERT INTO jobs VALUES(?,?,?,?,?)",
                ("job-002", "queued", None, 0, None),
            )
            connection.commit()
            connection.close()
            shutil.rmtree(proc / "123")
            exit_path = state / "deploy/workers/supervisors/job-001/exit.json"
            exit_path.write_text(
                json.dumps(
                    {
                        "schema_version": "poincare.job-supervisor-exit.v1",
                        "job_id": "job-001",
                        "finished_at": "2026-07-19T00:01:00Z",
                        "outcome": "process_exit",
                        "exit_code": 0,
                        "recorded_by": "supervisor",
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            exit_path.chmod(0o400)

            report = self.audit(state, proc)
            self.assertEqual(report.returncode, 0, report.stdout)
            payload = json.loads(report.stdout)
            self.assertEqual(payload["anomalies"], [])
            self.assertEqual(payload["live_supervisors"], 0)
            self.assertEqual(payload["active_jobs"][0]["state"], "reviewing")
            queued = run_bash(
                'source "$1"; POINCARE_STATE_DIR=$2; queued_job_count',
                str(state),
            )
            self.assertEqual(queued.returncode, 0, queued.stderr)
            self.assertEqual(queued.stdout.strip(), "1")

    def test_dead_exit_recorded_history_survives_config_upgrade(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state, proc, _ = self.make_fixture(Path(temporary).resolve())
            connection = sqlite3.connect(state / "harness.sqlite3")
            connection.execute(
                "UPDATE jobs SET state = 'passed', lease_expires_at = NULL"
            )
            connection.commit()
            connection.close()
            shutil.rmtree(proc / "123")
            launch_path = state / "deploy/workers/supervisors/job-001/launch.json"
            launch = json.loads(launch_path.read_text(encoding="utf-8"))
            launch["config_fingerprint"] = "previous-fingerprint"
            launch["capacity_slot"] = 4
            launch_path.chmod(0o600)
            launch_path.write_text(json.dumps(launch) + "\n", encoding="utf-8")
            launch_path.chmod(0o400)
            exit_path = launch_path.parent / "exit.json"
            exit_path.write_text(
                json.dumps(
                    {
                        "schema_version": "poincare.job-supervisor-exit.v1",
                        "job_id": "job-001",
                        "finished_at": "2026-07-19T00:01:00Z",
                        "outcome": "process_exit",
                        "exit_code": 0,
                        "recorded_by": "supervisor",
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            exit_path.chmod(0o400)

            report = self.audit(state, proc)
            self.assertEqual(report.returncode, 0, report.stdout)
            payload = json.loads(report.stdout)
            self.assertEqual(payload["anomalies"], [])
            self.assertEqual(payload["live_supervisors"], 0)


if __name__ == "__main__":
    unittest.main()
