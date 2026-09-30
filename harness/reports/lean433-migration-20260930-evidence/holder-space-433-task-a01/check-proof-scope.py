from pathlib import Path
import hashlib
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path("Poincare/Global/ParabolicHolderSpace.lean").read_text()
def mask(s):
 start=s.index("theorem isClosed_holderSubmodule :")
 body=s.index(":= by",start)+len(":= by")
 end=s.index("\ninstance instCompleteSpace",body)
 return s[:body]+"[PROOF]"+s[end:]
assert mask(base)==mask(actual),"change outside the one permitted closedness proof body"
print("PRESERVED_HOLDER_DEFINITIONS_AND_OTHER_PROOFS",hashlib.sha256(mask(actual).encode()).hexdigest())
