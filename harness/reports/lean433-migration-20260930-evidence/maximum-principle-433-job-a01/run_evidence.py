from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time
cwd=Path(__file__).resolve().parents[5]
job=Path(__file__).resolve().parent
label=sys.argv[1]; argv=sys.argv[2:]
assert argv and label and '/' not in label
attempt=job/label
attempt.mkdir(exist_ok=False)
source=cwd/'Poincare/MaximumPrinciple.lean'
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def git(args):return subprocess.run(['git',*args],cwd=cwd,text=True,capture_output=True).stdout
head=git(['rev-parse','HEAD']).strip()
source_before=source.read_bytes()
(attempt/'source-before.lean').write_bytes(source_before)
(attempt/'diff-before.patch').write_text(git(['diff','--','Poincare/MaximumPrinciple.lean']))
start=utc(); timer=time.monotonic()
(attempt/'start.json').write_text(json.dumps({'cwd':str(cwd),'argv':argv,'env_overrides':{'LEAN_NUM_THREADS':'1'},'head':head,'status':git(['status','--short','--branch']),'source_sha256':hashlib.sha256(source_before).hexdigest(),'started_at':start},indent=2)+'\n')
with (attempt/'output.log').open('x') as log:
 result=subprocess.run(argv,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=log,stderr=subprocess.STDOUT)
(attempt/'source-after.lean').write_bytes(source.read_bytes())
(attempt/'diff-after.patch').write_text(git(['diff','--','Poincare/MaximumPrinciple.lean']))
receipt={'cwd':str(cwd),'argv':argv,'head_before':head,'head_after':git(['rev-parse','HEAD']).strip(),'started_at':start,'ended_at':utc(),'duration_seconds':time.monotonic()-timer,'exit_code':result.returncode,'source_before_sha256':hashlib.sha256(source_before).hexdigest(),'source_after_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'status_after':git(['status','--short','--branch'])}
(attempt/'final.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
print((attempt/'output.log').read_text())
sys.exit(result.returncode)
