from pathlib import Path
import sys

state = Path(__file__).resolve().parent
baseline = (state / "frozen-base.lean").read_bytes()
candidate = Path(sys.argv[1] if len(sys.argv) > 1 else "Poincare/Global/HeatApproxIdentity.lean").read_bytes()
header = b"theorem tendsto_heatSolution_nhdsGT_zero {f : E \xe2\x86\x92 \xe2\x84\x9d} (hf : Integrable f)"
# Select the existing final declaration uniquely; preserve its complete header.
def masked(source):
    assert source.count(header) == 1, "final declaration missing or duplicated"
    start = source.index(header)
    body_start = source.index(b":= by", start) + len(b":= by")
    body_end = source.index(b"\nend Poincare", body_start)
    return source[:body_start] + b"[APPROVED_FINAL_PROOF_BODY]" + source[body_end:]
assert masked(baseline) == masked(candidate), "change outside approved final proof body"
print("PRESERVED_GAUSSIAN_MEASURE_COMPLEX_REAL_BRIDGE_PUBLIC_PRIVATE_HEADERS_AND_OTHER_PROOFS")
