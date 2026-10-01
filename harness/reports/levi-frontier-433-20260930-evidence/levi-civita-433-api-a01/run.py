from pathlib import Path
import subprocess,sys,json,datetime,os
p=Path(__file__).resolve().parent
label=sys.argv[1];cwd=Path(sys.argv[2]);source=p/sys.argv[3]
command=['env','LEAN_NUM_THREADS=1','lake','env','lean',str(source)]
started={'argv':command,'cwd':str(cwd),'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=cwd,text=True).strip(),'toolchain':(cwd/'lean-toolchain').read_text().strip(),'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(p/(label+'.started.json')).open('x').write(json.dumps(started,indent=2)+'\n')
with (p/(label+'.stdout.log')).open('x') as out,(p/(label+'.stderr.log')).open('x') as err:r=subprocess.run(command,cwd=cwd,stdout=out,stderr=err)
(p/(label+'.result.json')).open('x').write(json.dumps(dict(started,exit_code=r.returncode,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
print(label,'exit',r.returncode);print((p/(label+'.stdout.log')).read_text());print((p/(label+'.stderr.log')).read_text())
sys.exit(r.returncode)
