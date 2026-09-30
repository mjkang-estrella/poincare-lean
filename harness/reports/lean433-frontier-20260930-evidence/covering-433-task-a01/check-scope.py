from pathlib import Path
import re
p=Path(__file__).resolve().parent
base=(p/"frozen-base.lean").read_text().replace("LocPathConnectedSpace","LocallyPathConnectedSpace")
actual=Path("Poincare/Global/CoveringSkeleton.lean").read_text()
def headers(s):return re.findall(r"^(?:theorem|def)\s+[\w.]+[\s\S]*?(?=:=)",s,re.M)
assert headers(base)==headers(actual),"public type/header changed beyond proven class alias rename"
start="def homeomorphOfIsCoveringMapSimplyConnected"
assert base[base.index(start):]==actual[actual.index(start):],"bundled homeomorphism data or body changed"
print("PRESERVED_COVERING_TYPES_AND_HOMEOMORPH_DATA")
