from pathlib import Path
import subprocess, json, hashlib, datetime, time, sys
worker=Path("/Users/mjkang/.codex/worktrees/heat-pden-433/poincare")
root=Path(__file__).resolve().parent
state=Path("/Users/mjkang/.codex/worktrees/incremental-verification/poincare")
task=json.loads((worker/"harness/v2/state/upstream-verification-20260930/heat-pden-433-task-a02/task.json").read_text())
sys.path.insert(0,str(worker))
from harness.v2.runtime.validation import validate_task, validate_statement_readback, validate_statement_pinned_sources
validate_task(task)
c=task["statement_contract"]
validate_statement_readback(c,(worker/c["review"]["report_path"]).read_bytes())
validate_statement_pinned_sources(c,worker)
head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=worker,text=True).strip()
assert head=="eae832136f97f5aa34a4fd7484d203b55503dd6e"
results=[]
for i,command in enumerate(task["acceptance"]["commands"]):
 d=root/f"gate-{i+1:02d}";d.mkdir();start=time.time()
 with (d/"stdout.log").open("wb") as out,(d/"stderr.log").open("wb") as err:
  r=subprocess.run(command,cwd=worker,stdout=out,stderr=err)
 ok=r.returncode==0 or (command[0]=="rg" and r.returncode==1 and (d/"stdout.log").stat().st_size==0)
 item={"command":command,"exit_code":r.returncode,"pass":ok,"seconds":time.time()-start,"source_head":head,"log_hashes":{n:hashlib.sha256((d/n).read_bytes()).hexdigest() for n in ["stdout.log","stderr.log"]}}
 (d/"result.json").write_text(json.dumps(item,indent=2)+"\n");results.append(item)
 print(i+1, "PASS" if ok else "FAIL",r.returncode,flush=True)
 if not ok:sys.exit(r.returncode or 1)
(root/"result.json").write_text(json.dumps({"source_head":head,"base_commit":task["base_commit"],"exit_code":0,"results":results},indent=2)+"\n")
