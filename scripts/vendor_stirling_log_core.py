"""Reproduce the pinned Mathlib Stirling Part 1 proof subset; never compiles."""
from pathlib import Path
import hashlib
import json
import re

def rendered_core(text):
    body=text[text.index('open scoped Topology Real Nat Asymptotics'):text.index('/-!\n### Part 2')]
    body=re.sub(r'@\[deprecated[^\n]*\]\nalias[^\n]*\n','',body)
    body=re.sub(r'@\[deprecated[^\n]*\] alias[^\n]*\n','',body)
    body=body.replace('namespace Stirling', 'namespace OddPiPowers.StirlingLogCore')
    header=text[:text.index('module')]
    return header+'module\n\npublic import Mathlib.Analysis.SpecialFunctions.Integrals.Basic\n\n'+\
        '/-! Pinned Mathlib Stirling Part 1 only. The Wallis/normalization part is not needed.\n'+\
        'See logs/p5e-stirling-core-provenance.json. -/\n\n@[expose] public section\n\n'+body+'\nend OddPiPowers.StirlingLogCore\n'

if __name__ == '__main__':
    project=Path(__file__).resolve().parents[1]/'formalization/OddPiPowers'
    src=project/'.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean'
    out=project/'OddPiPowers/Analysis/StirlingLogCore.lean'
    out.write_text(rendered_core(src.read_text(encoding='utf-8')),encoding='utf-8')
    record=dict(source='Mathlib/Analysis/SpecialFunctions/Stirling.lean',mathlib_version='v4.35.0',
        source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
        adapted='OddPiPowers/Analysis/StirlingLogCore.lean',
        adapted_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),
        license='Apache-2.0; original copyright header retained',
        changes=['retain Part 1 through positive-limit theorem only',
                 'replace missing Wallis import by its cached Integrals.Basic import',
                 'relocate namespace Stirling to OddPiPowers.StirlingLogCore',
                 'omit deprecated aliases; no proof changes'])
    (project/'logs/p5e-stirling-core-provenance.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
    print('Prepared pinned Stirling logarithmic core; no compiler started.')
