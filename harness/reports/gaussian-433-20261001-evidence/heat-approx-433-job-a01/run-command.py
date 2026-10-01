from pathlib import Path
import datetime, hashlib, json, subprocess, sys, time
job = Path(__file__).resolve().parent
label, *command = sys.argv[1:]
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
begin = time.monotonic()
proc = subprocess.run(command, capture_output=True)
for suffix, data in [("stdout", proc.stdout), ("stderr", proc.stderr)]:
    with (job / (label + "." + suffix)).open("xb") as f:
        f.write(data)
receipt = {"command":command,"cwd":str(Path.cwd()),"started_utc":started,"finished_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"elapsed_seconds":time.monotonic()-begin,"exit_code":proc.returncode,"stdout_sha256":hashlib.sha256(proc.stdout).hexdigest(),"stderr_sha256":hashlib.sha256(proc.stderr).hexdigest()}
with (job / (label + ".result.json")).open("x") as f:
    json.dump(receipt, f, indent=2)
    f.write("\n")
print(json.dumps(receipt))
sys.stdout.buffer.write(proc.stdout)
sys.stderr.buffer.write(proc.stderr)
sys.exit(proc.returncode)
