from pathlib import Path
import hashlib, importlib.util, json, re
p=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('scope_guard',p/'check-scope-a02.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
base=(p/'frozen-base.lean').read_bytes()
masked=m.masked(base)
start=base.index(b'theorem hasFDerivAt_stereoInvFunAuxFDeriv (v z : E) :')
a=base.index(b':= by',start)+len(b':= by')
positive=base[:a]+b'\n  skip'+base[a:]
assert m.masked(positive)==masked
negative={
 'conformal_factor_data':base.replace(b'16 / (',b'15 / (',1),
 'fderiv_data':base.replace(b'(8 * (',b'(7 * (',1),
 'public_header':base.replace(b'theorem hasFDerivAt_stereoInvFunAuxFDeriv (v z : E) :',b'theorem hasFDerivAt_stereoInvFunAuxFDeriv (v z : E) (h : True) :',1),
 'other_proof':base.replace(b'(hasFDerivAt_stereoInvFunAuxFDeriv v z).fderiv',b'(hasFDerivAt_stereoInvFunAuxFDeriv v z).fderiv ',1),
 'import':base.replace(b'import Poincare.Global.RoundSphereMetric',b'import Poincare.Global.Statement',1),
 'hidden_declaration':base[:a]+b'\n  theorem hidden : True := by trivial'+base[a:],
 'hidden_namespace':base[:a]+b'\nnamespace Hidden'+base[a:]
}
rejected=[]
for label,source in negative.items():
 try: ok=m.masked(source)==masked
 except (AssertionError,ValueError):ok=False
 assert not ok,label+' escaped proof-only guard'
 rejected.append(label)
log=(p/'original-probe-a01.stdout.log').read_text()
assert log.count('FROZEN_CONTRACT_OK:')==8
assert log.count('AXIOM_CONTRACT_OK:')==8
closure=re.search(r'TRANSITIVE_SAFETY_OK: visited=(\d+), recursor_rules=(\d+), inductive_constructors=(\d+)',log)
assert closure and all(int(x)>0 for x in closure.groups())
for label,expected in [('export-types-a01',0),('original-probe-a01',0),('original-source-a01',0),('original-forbidden-scan-a01',1),('original-diff-check-a01',0),('scope-baseline-a01',0)]:
 result=json.loads((p/(label+'.result.json')).read_text())
 assert result['exit_code']==expected,label
 for stream in ['stdout','stderr']:
  actual=hashlib.sha256((p/(label+'.'+stream+'.log')).read_bytes()).hexdigest()
  assert actual==result[stream+'_sha256'],label+' log hash mismatch'
scan=(p/'original-forbidden-scan-a01.stdout.log').read_bytes()
assert scan==b''
snapshot=json.loads((p/'blind-snapshot-a02.json').read_text())
canonical={k:snapshot[k] for k in ['imports','declarations','definition_files']}
digest=hashlib.sha256(json.dumps(canonical,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
assert digest==snapshot['snapshot_sha256']
original=json.loads((p/'raw-original-types.json').read_text())
assert snapshot['declarations']==[{k:d[k] for k in ['name','lean_type','universes']} for d in original]
print(json.dumps({'positive_proof_body_change_accepted':True,'negative_changes_rejected':rejected,'type_checks':8,'axiom_checks':8,'transitive_visited':int(closure[1]),'recursor_rules':int(closure[2]),'inductive_constructors':int(closure[3]),'snapshot_sha256':digest}))
