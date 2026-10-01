from pathlib import Path
import hashlib
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path('Poincare/Global/SmoothInitialMetricDefinitions.lean').read_text()
ranges=[('theorem localEuclideanInner_apply', '\nend Poincare.SmoothInitialMetricDefinitions')]
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
