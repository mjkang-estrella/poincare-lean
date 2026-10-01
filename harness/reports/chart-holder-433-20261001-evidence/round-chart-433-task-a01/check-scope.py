from pathlib import Path
import hashlib, json, sys
p=Path(__file__).resolve().parent
BASE_SHA = '07a56718abd54fb15e55ce7e5497cffb2e3e59618fa7585a46fbc0caf71ea103'
MASK_SHA = '4cf48e55d33309bbb7415620511fb8785f50b0c1d1744aeb4234a76705e84d49'
PINS = [{'path': 'lean-toolchain', 'sha256': '3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71'}, {'path': 'lakefile.lean', 'sha256': '35024779083c3c1ab283349fe94cf6e7e8a59658132f05bc9ef8479d11d7e398'}, {'path': 'lake-manifest.json', 'sha256': '1d7b430e56fad6141cc360d6684f8259ec40e8412bb9017a34e741e78dea4411'}, {'path': 'Poincare/Statement.lean', 'sha256': '6d47b786da5f6e5ead1eea7293c24e7d3903c07011eee1e9909b97bdc19d30e7'}, {'path': 'Poincare/Global/RiemannianContext.lean', 'sha256': '735a43227e216688b739d8a09ca613da72f07f3acfe3b4f5d8d7feaab662705a'}, {'path': 'Poincare/Global/RoundSphereMetric.lean', 'sha256': '3708d528df92dd840e68f48c7f458c341cc8093b1f692cd503b31e77edd51541'}, {'path': 'Poincare.lean', 'sha256': '4bde26abfe162616f63c805d01522d357fcec811447103db17c68c10a6e5f224'}]
def digest(raw): return hashlib.sha256(raw).hexdigest()
def masked(raw):
 start=b'theorem hasFDerivAt_stereoInvFunAuxFDeriv (v z : E) :'
 assert raw.count(start)==1, 'missing or duplicate frozen declaration'
 a=raw.index(start)
 b=raw.index(b':= by',a)+len(b':= by')
 c=raw.index(b'\ntheorem fderiv_stereoInvFunAux (v z : E)',b)
 return raw[:b]+b'[PERMITTED_PROOF_BODY]'+raw[c:]
def main():
 base=(p/'frozen-base.lean').read_bytes()
 actual=Path('Poincare/Global/RoundSphereChart.lean').read_bytes()
 assert digest(base)==BASE_SHA, 'frozen original source changed'
 assert digest(masked(base))==MASK_SHA
 assert masked(base)==masked(actual), 'change outside sole permitted proof body'
 for item in PINS:
  assert digest(Path(item['path']).read_bytes())==item['sha256'], 'target configuration/context pin changed: '+item['path']
 print('PRESERVED_FULL_SURROUNDING_SOURCE',digest(masked(actual)))
 print('TARGET_CONFIGURATION_AND_RETAINED_ROOT_PINS_OK',len(PINS))
if __name__=='__main__': main()
