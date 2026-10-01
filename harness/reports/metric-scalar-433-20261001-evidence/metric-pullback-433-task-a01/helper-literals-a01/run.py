from pathlib import Path
import json,subprocess,sys,datetime
q=Path(__file__).resolve().parent;label=sys.argv[1];source=q/sys.argv[2]
argv=['env','LEAN_NUM_THREADS=1','lake','env','lean',str(source)]
start={'argv':argv,'cwd':str(Path.cwd()),'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'toolchain':Path('lean-toolchain').read_text().strip(),'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(q/(label+'.started.json')).open('x').write(json.dumps(start,indent=2)+'\n')
with (q/(label+'.stdout.log')).open('x') as out,(q/(label+'.stderr.log')).open('x') as err:r=subprocess.run(argv,stdout=out,stderr=err)
(q/(label+'.result.json')).open('x').write(json.dumps(dict(start,exit_code=r.returncode,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
print('exit',r.returncode);print((q/(label+'.stdout.log')).read_text());print((q/(label+'.stderr.log')).read_text());sys.exit(r.returncode)
