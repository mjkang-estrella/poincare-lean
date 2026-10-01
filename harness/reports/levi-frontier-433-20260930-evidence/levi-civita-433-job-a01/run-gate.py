from pathlib import Path
import sys,subprocess,json,datetime,os
job=Path(__file__).resolve().parent;a=job/sys.argv[1];a.mkdir(exist_ok=False);argv=sys.argv[2:]
(a/'source.lean').open('x').write(Path('Poincare/LeviCivitaUniqueness.lean').read_text())
(a/'diff.patch').open('x').write(subprocess.check_output(['git','diff','88f9d463817418be93153be8a137570854b9dad4','--','Poincare/LeviCivitaUniqueness.lean'],text=True))
started={'argv':argv,'cwd':str(Path.cwd()),'base_commit':'88f9d463817418be93153be8a137570854b9dad4','head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(a/'started.json').open('x').write(json.dumps(started,indent=2)+'\n')
with (a/'stdout.log').open('x') as out,(a/'stderr.log').open('x') as err:r=subprocess.run(argv,stdout=out,stderr=err,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
(a/'result.json').open('x').write(json.dumps(dict(started,exit_code=r.returncode,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
print('RESULT',a.name,r.returncode);print((a/'stdout.log').read_text());print((a/'stderr.log').read_text());sys.exit(r.returncode)
