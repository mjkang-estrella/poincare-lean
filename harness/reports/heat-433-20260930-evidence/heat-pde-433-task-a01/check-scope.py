from pathlib import Path
import re
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path("Poincare/Global/HeatKernelPDE.lean").read_text()
def headers(s):return re.findall(r"^(?:private )?(?:theorem|lemma|def)\s+[\w.]+[\s\S]*?(?=:=)",s,re.M)
assert headers(base)==headers(actual),"public or private type/header changed"
def field(s):return s[s.index("def heatKernelReal"):s.index("\ntheorem heatKernel_real_eq")]
assert field(base)==field(actual),"Gaussian kernel data changed"
assert base[:base.index("private lemma")]==actual[:actual.index("private lemma")],"imports or section declarations changed"
print("PRESERVED_HEAT_PDE_TYPES_AND_GAUSSIAN_DATA")
