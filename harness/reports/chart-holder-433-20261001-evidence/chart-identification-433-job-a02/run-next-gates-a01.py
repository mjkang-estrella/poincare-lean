from pathlib import Path
import subprocess,json,hashlib,time,datetime,sys
root=Path.cwd();job=root/'harness/v2/state/upstream-verification-20260930/chart-identification-433-job-a02';source=root/'Poincare/ChartIdentification.lean';sha=lambda b:hashlib.sha256(b).hexdigest();frozen='87837de15a778da5c137decbdd9dcbf086b3fcb40171c5f42c643d3876468489'
commands=[
 ('gate-build-a01',['env','LEAN_NUM_THREADS=1','lake','build','Poincare.ChartIdentification'],0),
 ('gate-formula-frozen-a01',['env','LEAN_NUM_THREADS=1','lake','env','lean','harness/v2/state/upstream-verification-20260930/chart-identification-433-task-a01/CurrentFormulaFrozenProbe-a03.lean'],0),
 ('gate-explicit-frozen-a01',['env','LEAN_NUM_THREADS=1','lake','env','lean','harness/v2/state/upstream-verification-20260930/chart-identification-433-task-a01/CurrentExplicitFrozenProbe-a03.lean'],0),
 ('gate-scope-a01',['python3','harness/v2/state/upstream-verification-20260930/chart-successor-scope-a01/check-scope-a02.py'],0),
 ('gate-scope-selftest-a01',['python3','harness/v2/state/upstream-verification-20260930/chart-successor-scope-a01/check-scope-a02.py','--self-test'],0),
 ('gate-tokens-a01',['rg','-n',r'\b(sorry|admit|axiom)\b|native_decide','Poincare/ChartIdentification.lean'],1),
 ('gate-added-source-tokens-a01',['rg','-n',r'\b(sorry|admit|axiom|postulate|native_decide|unsafe|partial|set_option|letI|haveI)\b','Poincare/ChartIdentification.lean'],1),
 ('gate-diff-a01',['git','diff','--check'],0)]
for name,cmd,expected in commands:
 assert sha(source.read_bytes()) == frozen
 start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
 with (job/(name+'.stdout.log')).open('xb') as out,(job/(name+'.stderr.log')).open('xb') as err:
  p=subprocess.run(cmd,cwd=root,stdout=out,stderr=err)
 result={'name':name,'command':cmd,'cwd':str(root),'started_at':start,'finished_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':p.returncode,'duration_seconds':time.monotonic()-t,'expected_exit':expected,'passed':p.returncode==expected,'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'source_sha256':sha(source.read_bytes()),'stdout_sha256':sha((job/(name+'.stdout.log')).read_bytes()),'stderr_sha256':sha((job/(name+'.stderr.log')).read_bytes())}
 with (job/(name+'.result.json')).open('x') as f:json.dump(result,f,indent=2);f.write('\n')
 print(json.dumps({k:result[k] for k in ['name','exit_code','expected_exit','passed','duration_seconds']}),flush=True)
 if not result['passed']:
  print((job/(name+'.stdout.log')).read_text(),(job/(name+'.stderr.log')).read_text());sys.exit(1)
