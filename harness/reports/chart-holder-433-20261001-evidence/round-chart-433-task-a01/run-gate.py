from pathlib import Path
import hashlib, json, os, subprocess, sys, time
p=Path(__file__).resolve().parent
label=sys.argv[1]
cwd=sys.argv[2]
cmd=sys.argv[3:]
assert label and all(c.isalnum() or c in '-_' for c in label)
for suffix in ['started.json','stdout.log','stderr.log','result.json']:
 assert not (p/(label+'.'+suffix)).exists(), 'append-only attempt already exists'
def save(name,obj): (p/(label+'.'+name)).write_text(json.dumps(obj,indent=2)+'\n')
started=time.time()
save('started.json',{'started_epoch':started,'cwd':cwd,'argv':cmd,'environment':{'LEAN_NUM_THREADS':'1'}})
with (p/(label+'.stdout.log')).open('wb') as out, (p/(label+'.stderr.log')).open('wb') as err:
 result=subprocess.run(cmd,cwd=cwd,stdout=out,stderr=err,env=dict(os.environ,LEAN_NUM_THREADS='1'))
save('result.json',{'exit_code':result.returncode,'started_epoch':started,'ended_epoch':time.time(),'elapsed_seconds':time.time()-started,'cwd':cwd,'argv':cmd,'stdout_sha256':hashlib.sha256((p/(label+'.stdout.log')).read_bytes()).hexdigest(),'stderr_sha256':hashlib.sha256((p/(label+'.stderr.log')).read_bytes()).hexdigest()})
print(json.dumps({'attempt':label,'exit_code':result.returncode,'elapsed_seconds':time.time()-started}))
sys.exit(result.returncode)
