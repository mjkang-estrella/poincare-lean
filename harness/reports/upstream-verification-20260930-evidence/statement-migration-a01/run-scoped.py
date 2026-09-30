import pathlib,subprocess,json,time,datetime,os,sys
root=pathlib.Path(__file__).parent
p=root/sys.argv[1];p.mkdir()
src=pathlib.Path('/Users/mjkang/.codex/worktrees/statement-433-migration/poincare/Poincare/Statement.lean')
(p/'Statement.lean').write_bytes(src.read_bytes())
argv=['lake','env','lean','-DmaxErrors=1000',str(src)]
cwd='/Users/mjkang/.codex/external-reviews/poincare-20260930/dg-v013-verification'
(p/'argv.json').write_text(json.dumps({'argv':argv,'cwd':cwd,'env':{'LEAN_NUM_THREADS':'1'},'start':datetime.datetime.now(datetime.UTC).isoformat()},indent=2))
(p/'diff.patch').write_bytes(subprocess.check_output(['git','diff','--','Poincare/Statement.lean'],cwd=src.parent.parent))
start=time.monotonic()
with (p/'stdout.log').open('wb') as out,(p/'stderr.log').open('wb') as err:r=subprocess.run(argv,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=out,stderr=err)
(p/'result.json').write_text(json.dumps({'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-start,'end':datetime.datetime.now(datetime.UTC).isoformat()},indent=2))
print((p/'result.json').read_text())
