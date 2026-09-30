from pathlib import Path
import re
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text()
actual=Path("Poincare/Global/GeodesicChart.lean").read_text()
def headers(s):return re.findall(r"^(?:theorem|def)\s+[\w.]+[\s\S]*?(?=:=)",s,re.M)
assert headers(base)==headers(actual),"public type/header changed"
def field(s):return s[s.index("def geodesicFlowField"):s.index("@[simp]")]
assert field(base)==field(actual),"geodesic dynamics data changed"
print("PRESERVED_GEODESIC_TYPES_AND_FLOW_DATA")
