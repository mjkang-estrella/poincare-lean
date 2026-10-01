from pathlib import Path
import subprocess,sys,json,datetime,os,time,hashlib
p=Path(__file__).resolve().parent
label=sys.argv[1];cwd=Path(sys.argv[2]);source=p/sys.argv[3];pin=sys.argv[4]
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=cwd,text=True).strip()
if head != pin:
 raise SystemExit('Refusing probe due to source HEAD drift: '+head)
command=['env','LEAN_NUM_THREADS=1','lake','env','lean',str(source)]
started={'argv':command,'cwd':str(cwd),'head':head,'toolchain':(cwd/'lean-toolchain').read_text().strip(),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'lake_manifest_sha256':hashlib.sha256((cwd/'lake-manifest.json').read_bytes()).hexdigest(),'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'invocation_kind':'cached direct Lean; no build'}
(p/(label+'.started.json')).open('x').write(json.dumps(started,indent=2)+'\n')
begin=time.monotonic()
with (p/(label+'.stdout.log')).open('x') as out,(p/(label+'.stderr.log')).open('x') as err:
 r=subprocess.run(command,cwd=cwd,stdout=out,stderr=err)
finish=dict(started,exit_code=r.returncode,seconds=time.monotonic()-begin,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
finish['log_hashes']={n:hashlib.sha256((p/n).read_bytes()).hexdigest() for n in [label+'.stdout.log',label+'.stderr.log']}
(p/(label+'.result.json')).open('x').write(json.dumps(finish,indent=2)+'\n')
print(label,'exit',r.returncode,'seconds',round(finish['seconds'],2));print((p/(label+'.stdout.log')).read_text());print((p/(label+'.stderr.log')).read_text())
sys.exit(r.returncode)
