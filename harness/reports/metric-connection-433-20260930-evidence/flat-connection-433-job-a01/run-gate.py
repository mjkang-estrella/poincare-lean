from pathlib import Path
import sys, subprocess, json, datetime, os
job=Path(__file__).resolve().parent
label=sys.argv[1]; argv=sys.argv[2:]
a=job/label;a.mkdir(exist_ok=False)
(a/'source.lean').open('x').write(Path('Poincare/FlatModelConnection.lean').read_text())
(a/'diff.patch').open('x').write(subprocess.check_output(['git','diff','37628ffa5cf60c2ab90994452279aaf1bc82dab4','--','Poincare/FlatModelConnection.lean'],text=True))
started={'argv':argv,'cwd':str(Path.cwd()),'base_commit':'37628ffa5cf60c2ab90994452279aaf1bc82dab4','head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(a/'started.json').open('x').write(json.dumps(started,indent=2)+'\n')
with (a/'stdout.log').open('x') as out,(a/'stderr.log').open('x') as err:
 p=subprocess.run(argv,stdout=out,stderr=err,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
(a/'result.json').open('x').write(json.dumps(dict(started,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=p.returncode),indent=2)+'\n')
print('RESULT',label,p.returncode)
print((a/'stdout.log').read_text())
print((a/'stderr.log').read_text())
sys.exit(p.returncode)
