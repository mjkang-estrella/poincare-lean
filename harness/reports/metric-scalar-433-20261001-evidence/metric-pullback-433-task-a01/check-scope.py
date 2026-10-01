from pathlib import Path
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path("Poincare/Global/SmoothInitialMetricLocalPullback.lean").read_text()
def masked(s):
 a=s.index("theorem localEuclideanInner_coordinates")
 b=s.index(":= by",a)+len(":= by")
 c=s.index("\nset_option synthInstance.maxHeartbeats",b)
 return s[:b]+"[PROOF]"+s[c:]
assert masked(base)==masked(actual),"change outside coordinate proof body"
print("PRESERVED_METRIC_PULLBACK_ALL_OTHER_DATA_TYPES_PROOFS")
