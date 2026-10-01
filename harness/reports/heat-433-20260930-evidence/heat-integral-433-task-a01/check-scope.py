from pathlib import Path
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path("Poincare/Global/HeatKernelIntegral.lean").read_text()
def masked(s):
 a=s.index("theorem gaussianApproxIdentity_heatTimeScale_complex")
 b=s.index(":= by",a)+len(":= by")
 c=s.index("\nend Poincare",b)
 return s[:b]+"[PROOF]"+s[c:]
assert masked(base)==masked(actual),"change outside one permitted proof body"
print("PRESERVED_HEAT_INTEGRAL_DATA_AND_OTHER_PROOFS")
