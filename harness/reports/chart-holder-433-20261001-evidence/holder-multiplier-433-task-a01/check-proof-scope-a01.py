from pathlib import Path
import hashlib,json,subprocess,re
state=Path(__file__).resolve().parent
source_path="Poincare/Global/ParabolicHolderMultiplier.lean"
base=(state/"frozen-base.lean").read_bytes()
actual=Path(source_path).read_bytes()
spans=json.loads((state/"allowed-proof-spans-a01.json").read_text())["allowed_proof_bodies"]
def mask(data):
    edits=[]
    for span in spans:
        start_marker=span["start_marker"].encode()
        end_marker=span["end_marker"].encode()
        assert data.count(start_marker)==1 and data.count(end_marker)==1,"target boundary changed or duplicated"
        start=data.index(start_marker)
        body=data.index(b":= by",start)+len(b":= by")
        end=data.index(end_marker,body)
        assert hashlib.sha256(data[start:body]).hexdigest()==span["header_sha256"],"frozen target header changed"
        fragment=data[body:end]
        for line in fragment.splitlines():
            assert not line.strip() or line.startswith((b" ",b"\t")),"top-level insertion in allowed proof body"
        assert not re.search(rb"\b(?:sorry|admit|axiom|postulate|native_decide|unsafe|partial|run_cmd|run_tac|IO|include_str|include_bytes)\b|#(?:eval|reduce)\b",fragment),"forbidden proof-body token"
        edits.append((body,end,span["name"]))
    for body,end,name in sorted(edits,reverse=True):
        data=data[:body]+("[FROZEN_PROOF_BODY:"+name+"]").encode()+data[end:]
    return data
assert mask(actual)==mask(base),"change outside the two permitted tactic proof bodies"
pins=json.loads((state/"identity-a01.json").read_text())["new_definition_pins"]
for pin in pins:
    assert hashlib.sha256(Path(pin["path"]).read_bytes()).hexdigest()==pin["sha256"],"frozen definition/config changed: "+pin["path"]
changed=subprocess.check_output(["git","diff","--name-only"],text=True).splitlines()
assert all(p==source_path for p in changed),"tracked changes outside the task scope"
assert not subprocess.check_output(["git","ls-files","--others","--exclude-standard"],text=True).strip(),"untracked nonignored files outside task scope"
print("PRESERVED_MULTIPLIER_DATA_HEADERS_OTHER_PROOFS",hashlib.sha256(mask(actual)).hexdigest())
print("PINNED_MODELS_GRAPH_HOLDER_NORMS_SUPPORT_CONFIG_OK")
