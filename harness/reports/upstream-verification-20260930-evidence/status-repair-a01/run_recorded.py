from pathlib import Path
import datetime as dt
import json
import subprocess
import sys
import time

base = Path(__file__).resolve().parent
label, *argv = sys.argv[1:]
root = Path("/Users/mjkang/.codex/worktrees/completion-status-contract/poincare")
started_at = dt.datetime.now(dt.timezone.utc).isoformat()
started = time.monotonic()
with (base / (label + ".out")).open("xb") as output:
    result = subprocess.run(argv, cwd=root, stdout=output, stderr=subprocess.STDOUT, check=False)
record = {"argv": argv, "cwd": str(root), "started_at": started_at, "finished_at": dt.datetime.now(dt.timezone.utc).isoformat(), "duration_seconds": time.monotonic() - started, "exit_code": result.returncode}
with (base / (label + ".json")).open("x") as output:
    json.dump(record, output, indent=2)
print((base / (label + ".out")).read_text(), end="")
print(json.dumps(record))
sys.exit(result.returncode)
