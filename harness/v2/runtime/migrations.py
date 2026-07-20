"""SQLite migrations for the Harness v2 control-plane store."""

from __future__ import annotations

import sqlite3
from collections.abc import Sequence


SCHEMA_VERSION = 5


MIGRATIONS: Sequence[tuple[int, str, Sequence[str]]] = (
    (
        1,
        "initial_task_job_and_lease_store",
        (
            """
            CREATE TABLE tasks (
                task_id TEXT NOT NULL,
                revision INTEGER NOT NULL CHECK (revision >= 1),
                state TEXT NOT NULL CHECK (
                    state IN ('proposed', 'ready', 'active', 'accepted', 'blocked', 'superseded')
                ),
                base_commit TEXT NOT NULL,
                source_json TEXT NOT NULL,
                source_sha256 TEXT NOT NULL,
                accepted_commit TEXT,
                accepted_gate_job_id TEXT,
                blocked_reason TEXT,
                blocked_evidence_job_id TEXT,
                superseding_task_id TEXT,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                PRIMARY KEY (task_id, revision)
            )
            """,
            """
            CREATE TABLE task_events (
                sequence INTEGER PRIMARY KEY AUTOINCREMENT,
                task_id TEXT NOT NULL,
                revision INTEGER NOT NULL,
                event TEXT NOT NULL,
                from_state TEXT,
                to_state TEXT,
                details_json TEXT NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY (task_id, revision) REFERENCES tasks(task_id, revision)
            )
            """,
            """
            CREATE TABLE jobs (
                job_id TEXT PRIMARY KEY,
                task_id TEXT NOT NULL,
                task_revision INTEGER NOT NULL,
                attempt INTEGER NOT NULL CHECK (attempt >= 1),
                state TEXT NOT NULL CHECK (
                    state IN (
                        'queued', 'preparing', 'running', 'reviewing',
                        'passed', 'rejected', 'blocked', 'interrupted'
                    )
                ),
                source_json TEXT NOT NULL,
                source_sha256 TEXT NOT NULL,
                artifact_dir TEXT NOT NULL UNIQUE,
                lease_owner TEXT,
                lease_expires_at REAL,
                lease_generation INTEGER NOT NULL DEFAULT 0,
                started_at TEXT,
                heartbeat_at TEXT,
                finished_at TEXT,
                exit_reason TEXT,
                gate_status TEXT NOT NULL CHECK (gate_status IN ('not_run', 'passed', 'failed')),
                gate_result_path TEXT,
                gate_result_sha256 TEXT,
                accepted_commit TEXT,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                UNIQUE (task_id, task_revision, attempt),
                FOREIGN KEY (task_id, task_revision) REFERENCES tasks(task_id, revision)
            )
            """,
            """
            CREATE TABLE job_events (
                sequence INTEGER PRIMARY KEY AUTOINCREMENT,
                job_id TEXT NOT NULL,
                event TEXT NOT NULL,
                from_state TEXT,
                to_state TEXT,
                owner TEXT,
                details_json TEXT NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY (job_id) REFERENCES jobs(job_id)
            )
            """,
            """
            CREATE TABLE file_leases (
                scope TEXT PRIMARY KEY,
                literal_prefix TEXT NOT NULL,
                job_id TEXT NOT NULL,
                owner TEXT NOT NULL,
                generation INTEGER NOT NULL,
                acquired_at TEXT NOT NULL,
                heartbeat_at TEXT NOT NULL,
                expires_at REAL NOT NULL,
                FOREIGN KEY (job_id) REFERENCES jobs(job_id)
            )
            """,
            """
            CREATE TABLE lease_events (
                sequence INTEGER PRIMARY KEY AUTOINCREMENT,
                scope TEXT NOT NULL,
                job_id TEXT NOT NULL,
                owner TEXT NOT NULL,
                generation INTEGER NOT NULL,
                event TEXT NOT NULL CHECK (event IN ('acquired', 'renewed', 'recovered', 'released')),
                expires_at REAL NOT NULL,
                created_at TEXT NOT NULL
            )
            """,
            """
            CREATE TABLE artifact_entries (
                job_id TEXT NOT NULL,
                name TEXT NOT NULL,
                path TEXT NOT NULL,
                sha256 TEXT NOT NULL,
                created_at TEXT NOT NULL,
                PRIMARY KEY (job_id, name),
                FOREIGN KEY (job_id) REFERENCES jobs(job_id)
            )
            """,
            "CREATE INDEX task_state_index ON tasks(state, task_id, revision)",
            "CREATE INDEX job_queue_index ON jobs(state, created_at, job_id)",
            "CREATE INDEX job_task_index ON jobs(task_id, task_revision, attempt)",
            "CREATE INDEX lease_expiry_index ON file_leases(expires_at)",
            """
            CREATE TRIGGER task_events_no_update
            BEFORE UPDATE ON task_events
            BEGIN
                SELECT RAISE(ABORT, 'task_events are append-only');
            END
            """,
            """
            CREATE TRIGGER task_events_no_delete
            BEFORE DELETE ON task_events
            BEGIN
                SELECT RAISE(ABORT, 'task_events are append-only');
            END
            """,
            """
            CREATE TRIGGER job_events_no_update
            BEFORE UPDATE ON job_events
            BEGIN
                SELECT RAISE(ABORT, 'job_events are append-only');
            END
            """,
            """
            CREATE TRIGGER job_events_no_delete
            BEFORE DELETE ON job_events
            BEGIN
                SELECT RAISE(ABORT, 'job_events are append-only');
            END
            """,
            """
            CREATE TRIGGER lease_events_no_update
            BEFORE UPDATE ON lease_events
            BEGIN
                SELECT RAISE(ABORT, 'lease_events are append-only');
            END
            """,
            """
            CREATE TRIGGER lease_events_no_delete
            BEFORE DELETE ON lease_events
            BEGIN
                SELECT RAISE(ABORT, 'lease_events are append-only');
            END
            """,
            """
            CREATE TRIGGER artifact_entries_no_update
            BEFORE UPDATE ON artifact_entries
            BEGIN
                SELECT RAISE(ABORT, 'artifact registrations are append-only');
            END
            """,
            """
            CREATE TRIGGER artifact_entries_no_delete
            BEFORE DELETE ON artifact_entries
            BEGIN
                SELECT RAISE(ABORT, 'artifact registrations are append-only');
            END
            """,
        ),
    ),
    (
        2,
        "trusted_roots_and_codex_review",
        (
            "ALTER TABLE jobs ADD COLUMN reviewer_identity TEXT",
            "ALTER TABLE jobs ADD COLUMN reviewed_at TEXT",
            """
            CREATE TABLE runtime_config (
                singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
                worktree_root TEXT NOT NULL,
                integration_root TEXT NOT NULL,
                configured_at TEXT NOT NULL
            )
            """,
        ),
    ),
    (
        3,
        "reviewed_commit_tree_binding",
        ("ALTER TABLE jobs ADD COLUMN accepted_tree TEXT",),
    ),
    (
        4,
        "durable_dispatch_control",
        (
            """
            CREATE TABLE dispatch_control (
                singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
                desired_state TEXT NOT NULL CHECK (desired_state IN ('running', 'stopped')),
                generation INTEGER NOT NULL CHECK (generation >= 0),
                actor TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
            """,
            """
            INSERT INTO dispatch_control(singleton, desired_state, generation, actor, updated_at)
            VALUES (1, 'stopped', 0, 'schema-migration', '1970-01-01T00:00:00.000000Z')
            """,
            """
            CREATE TABLE dispatch_events (
                sequence INTEGER PRIMARY KEY AUTOINCREMENT,
                from_state TEXT NOT NULL CHECK (from_state IN ('running', 'stopped')),
                to_state TEXT NOT NULL CHECK (to_state IN ('running', 'stopped')),
                generation INTEGER NOT NULL CHECK (generation >= 1),
                actor TEXT NOT NULL,
                created_at TEXT NOT NULL
            )
            """,
            """
            CREATE TRIGGER dispatch_events_no_update
            BEFORE UPDATE ON dispatch_events
            BEGIN
                SELECT RAISE(ABORT, 'dispatch_events are append-only');
            END
            """,
            """
            CREATE TRIGGER dispatch_events_no_delete
            BEFORE DELETE ON dispatch_events
            BEGIN
                SELECT RAISE(ABORT, 'dispatch_events are append-only');
            END
            """,
        ),
    ),
    (
        5,
        "bind_job_leases_to_dispatch_generation",
        (
            """
            ALTER TABLE jobs
            ADD COLUMN lease_dispatch_generation INTEGER
            CHECK (lease_dispatch_generation IS NULL OR lease_dispatch_generation >= 0)
            """,
        ),
    ),
)


def migrate(connection: sqlite3.Connection, applied_at: str) -> int:
    """Apply every missing migration and return the resulting schema version."""

    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS schema_migrations (
            version INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            applied_at TEXT NOT NULL
        )
        """
    )
    row = connection.execute("SELECT MAX(version) AS version FROM schema_migrations").fetchone()
    current = 0 if row is None or row["version"] is None else int(row["version"])
    if current > SCHEMA_VERSION:
        raise RuntimeError(
            f"database schema {current} is newer than runtime schema {SCHEMA_VERSION}"
        )

    for version, name, statements in MIGRATIONS:
        if version <= current:
            continue
        connection.execute("BEGIN IMMEDIATE")
        try:
            # Another init process may have migrated while this connection was
            # waiting for the write lock. Re-read under that lock.
            locked_row = connection.execute(
                "SELECT MAX(version) AS version FROM schema_migrations"
            ).fetchone()
            locked_current = (
                0
                if locked_row is None or locked_row["version"] is None
                else int(locked_row["version"])
            )
            if locked_current >= version:
                connection.commit()
                current = locked_current
                continue
            if locked_current != version - 1:
                raise RuntimeError(
                    f"cannot apply schema migration {version} after {locked_current}"
                )
            for statement in statements:
                connection.execute(statement)
            connection.execute(
                "INSERT INTO schema_migrations(version, name, applied_at) VALUES (?, ?, ?)",
                (version, name, applied_at),
            )
            connection.execute(f"PRAGMA user_version = {version}")
            connection.commit()
        except Exception:
            connection.rollback()
            raise
        current = version
    return current
