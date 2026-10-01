import subprocess,json,time,datetime,hashlib,sys,os
from pathlib import Path
root=Path('/Users/mjkang/.codex/worktrees/incremental-verification/poincare/harness/v2/state/upstream-verification-20260930')
label=sys.argv[1];cwd=Path(sys.argv[2]);command=sys.argv[3:];d=root/label;d.mkdir(exist_ok=False)
meta={'command':command,'cwd':str(cwd),'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=cwd,text=True).strip(),'environment':{'LEAN_NUM_THREADS':'1'}}
(d/'started.json').write_text(json.dumps(meta,indent=2)+'\n');env=dict(os.environ,LEAN_NUM_THREADS='1');start=time.time()
with (d/'stdout.log').open('wb') as out,(d/'stderr.log').open('wb') as err:
 r=subprocess.run(command,cwd=cwd,env=env,stdout=out,stderr=err)
meta.update(exit_code=r.returncode,seconds=time.time()-start,completed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),log_hashes={f:hashlib.sha256((d/f).read_bytes()).hexdigest() for f in ['stdout.log','stderr.log']})
(d/'result.json').write_text(json.dumps(meta,indent=2)+'\n');print(label,'exit',r.returncode,'seconds',round(meta['seconds'],2),flush=True);sys.exit(r.returncode)
