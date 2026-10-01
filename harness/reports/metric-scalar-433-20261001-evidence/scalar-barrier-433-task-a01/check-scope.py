from pathlib import Path
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path("Poincare/Global/ScalarCurvatureBarrier.lean").read_text()
ranges=[("theorem hasDerivWithinAt_neg_inv","\n/-- If a negative function"),("theorem negative_reciprocal_growth_bound","\n/-- A nonnegative Riccati")]
def masked(s):
 spans=[]
 for start,end in ranges:
  a=s.index(start);b=s.index(":= by",a)+len(":= by");c=s.index(end,b);spans.append((b,c))
 for b,c in sorted(spans,reverse=True):s=s[:b]+"[PROOF]"+s[c:]
 return s
assert masked(base)==masked(actual),"change outside first two recorded proof bodies"
print("PRESERVED_SCALAR_BARRIER_ALL_TYPES_DATA_OTHER_PROOFS")
