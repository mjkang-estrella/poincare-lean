from pathlib import Path
import hashlib, json, os, subprocess, sys, time
p=Path(__file__).resolve().parent
label=sys.argv[1]
cmd=sys.argv[2:]
assert label and all(c.isalnum() or c in '-_' for c in label)
for suffix in ['started.json','stdout.log','stderr.log','result.json']:
 assert not (p/(label+'.'+suffix)).exists(), 'append-only receipt exists'
started=time.time()
(p/(label+'.started.json')).write_text(json.dumps({'started_epoch':started,'cwd':os.getcwd(),'argv':cmd,'environment':{'LEAN_NUM_THREADS':'1'}},indent=2)+'\n')
with (p/(label+'.stdout.log')).open('wb') as out, (p/(label+'.stderr.log')).open('wb') as err:
 result=subprocess.run(cmd,stdout=out,stderr=err,env=dict(os.environ,LEAN_NUM_THREADS='1'))
(p/(label+'.result.json')).write_text(json.dumps({'exit_code':result.returncode,'started_epoch':started,'ended_epoch':time.time(),'elapsed_seconds':time.time()-started,'cwd':os.getcwd(),'argv':cmd,'stdout_sha256':hashlib.sha256((p/(label+'.stdout.log')).read_bytes()).hexdigest(),'stderr_sha256':hashlib.sha256((p/(label+'.stderr.log')).read_bytes()).hexdigest()},indent=2)+'\n')
print(json.dumps({'attempt':label,'exit_code':result.returncode,'elapsed_seconds':time.time()-started}))
sys.exit(result.returncode)
