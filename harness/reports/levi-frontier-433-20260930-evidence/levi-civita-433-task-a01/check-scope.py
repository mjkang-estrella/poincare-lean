from pathlib import Path
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path("Poincare/LeviCivitaUniqueness.lean").read_text()
assert base.count("extDerivFun (fun")==6
expected=base.replace("extDerivFun (fun","mvfderiv I (fun")
assert actual==expected,"change beyond the six reviewed semantic-preserving derivative API normalizations"
print("PRESERVED_LEVI_DEFINITIONS_AND_ALL_PROOFS_MODULO_EXACT_DERIVATIVE_API_NORMALIZATION")
