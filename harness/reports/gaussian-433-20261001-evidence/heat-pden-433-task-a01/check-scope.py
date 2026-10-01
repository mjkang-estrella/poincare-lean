from pathlib import Path
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path("Poincare/Global/HeatKernelPDEn.lean").read_text()
ranges=[("theorem hasFDerivAt_neg_norm_sq_div", "\n/-- First spatial derivative of `exp"),("theorem iteratedFDeriv_two_exp_neg_norm_sq_div_apply", "\n/-- Parseval")]
def masked(s):
 spans=[]
 for start,end in ranges:
  a=s.index(start);b=s.index(":= by",a)+len(":= by");c=s.index(end,b);spans.append((b,c))
 for b,c in sorted(spans,reverse=True):s=s[:b]+"[PROOF]"+s[c:]
 return s
assert masked(base)==masked(actual),"change outside two approved proof bodies"
print("PRESERVED_GAUSSIAN_TYPES_DATA_PRIVATE_OTHER_PROOFS")
