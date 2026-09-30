from pathlib import Path
import datetime, hashlib, json, subprocess, sys, time
root = Path.cwd()
job = root / "harness/v2/state/upstream-verification-20260930/geodesic-433-job-a01"
attempt = job / sys.argv[1]
attempt.mkdir()
task = json.loads((job / "task-snapshot.json").read_text())
source = root / "Poincare/Global/GeodesicChart.lean"
(attempt / "source.lean").write_bytes(source.read_bytes())
(attempt / "diff.patch").write_bytes(subprocess.check_output(["git", "diff", "--", "Poincare/Global/GeodesicChart.lean"]))
results = []
labels = ["lean", "scoped-build", "frozen-probe", "scopeguard", "token-scan", "diff-check"]
job_started = datetime.datetime.fromisoformat(json.loads((job / "manifest-start.json").read_text())["started_utc"])
for label, argv in zip(labels, task["acceptance"]["commands"]):
    tick = time.monotonic()
    result = {"name": label, "cwd": str(root), "argv": argv, "base_sha": task["base_commit"], "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(), "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (attempt / (label + ".started.json")).write_text(json.dumps(result, indent=2) + "\n")
    elapsed_job = (datetime.datetime.now(datetime.timezone.utc) - job_started).total_seconds()
    with (attempt / (label + ".stdout")).open("wb") as out, (attempt / (label + ".stderr")).open("wb") as err:
        try:
            result["exit_code"] = subprocess.run(argv, cwd=root, stdout=out, stderr=err, timeout=max(1, 10800 - elapsed_job)).returncode
        except subprocess.TimeoutExpired:
            result["exit_code"] = 124
            err.write(b"Job wall-clock budget expired.\n")
    result["elapsed_seconds"] = time.monotonic() - tick
    result["completed_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result["passed"] = result["exit_code"] == (1 if label == "token-scan" else 0)
    if label == "token-scan":
        result["passed"] = result["passed"] and (attempt / (label + ".stdout")).stat().st_size == 0
    (attempt / (label + ".result.json")).write_text(json.dumps(result, indent=2) + "\n")
    results.append(result)
    print(json.dumps({"name": label, "exit_code": result["exit_code"], "elapsed_seconds": round(result["elapsed_seconds"], 2), "passed": result["passed"]}), flush=True)
    if label in ["frozen-probe", "scopeguard"] or not result["passed"]:
        print((attempt / (label + ".stdout")).read_text(), flush=True)
        print((attempt / (label + ".stderr")).read_text(), flush=True)
    if not result["passed"]:
        break
receipt = {"cwd": str(root), "base_sha": task["base_commit"], "head_after": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(), "status_after": subprocess.check_output(["git", "status", "--short", "--branch"], text=True), "all_scoped_gates_passed": len(results) == len(labels) and all(r["passed"] for r in results), "results": results}
(attempt / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps({"all_scoped_gates_passed": receipt["all_scoped_gates_passed"], "evidence": str(attempt), "status_after": receipt["status_after"]}), flush=True)
