from pathlib import Path
import hashlib
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path('Poincare/Global/RoundSphereMetric.lean').read_text()
ranges=[('theorem roundSphereMetric3_inner_apply', '\ntheorem roundSphereMetric3_inner_mfderiv_eq'), ('theorem roundSphereMetric3_inner_mfderiv_eq', '\ntheorem roundSphereMetric3_inner_symm'), ('theorem roundSphereMetric3_modelInner_contDiff', '\ntheorem roundSphereMetric3_inner_contMDiff'), ('theorem roundSphereMetric3_inner_contMDiff', '\nnoncomputable def roundSphereMetric3 :')]
def masked(s):
 spans=[]
 for start,end in ranges:
  a=s.index(start)
  if start.endswith(" := by"):
   b=a+len(start)
  else:
   b=s.index(":= by",a)+len(":= by")
  c=s.index(end,b)
  spans.append((b,c))
 for b,c in sorted(spans,reverse=True):s=s[:b]+"[PERMITTED_PROOF_BODY]"+s[c:]
 return s
assert masked(base)==masked(actual),"change outside permitted proof bodies or normative data/header change"
print("PRESERVED_FULL_SURROUNDING_SOURCE",hashlib.sha256(masked(actual).encode()).hexdigest())
