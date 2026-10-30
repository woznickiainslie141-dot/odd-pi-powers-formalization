"""Prepare exact P5-E/P6-A declaration and regression audits; never compiles."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent.parent
project = root / 'formalization/OddPiPowers'
files = ['Analysis/'+s for s in ['GridIntegralBound', 'CentralLogLipschitz',
    'ScaledGridLimit', 'StirlingLogCore', 'FactorialLogRate', 'ScaledIntervalRate',
    'ActualCentralRate', 'CommonScaleRate', 'CentralRemainderRate', 'TwelveLayerCentralRate']]
files += ['Transfer/RationalRateCertificate']
names, hashes = [], {}
for filename in files:
    path = project / f'OddPiPowers/{filename}.lean'
    hashes[str(path.relative_to(project))] = hashlib.sha256(path.read_bytes()).hexdigest()
    stack = []
    for line in path.read_text(encoding='utf-8').splitlines():
        ns = re.match(r'^namespace (\S+)', line)
        end = re.match(r'^end (\S+)', line)
        decl = re.match(r'^(?:noncomputable )?(def|theorem|lemma) ([\w.\']+)', line)
        if ns:
            stack.append(ns.group(1))
        elif end:
            assert stack.pop() == end.group(1), (path, line)
        elif decl:
            names.append('.'.join([*stack, decl.group(2)]))
    assert not stack, path
assert len(names) == len(set(names)) == 50
old = json.loads((project / 'logs/p5d-audit-expected.json').read_text(encoding='utf-8'))
regression = old['regression'] + old['new']
assert len(regression) == len(set(regression)) == 471
assert not set(names).intersection(regression)
for file, imports, values in [
    ('P5EAxiomAudit.lean', ['OddPiPowers.Analysis.TwelveLayerCentralRate',
                          'OddPiPowers.Transfer.RationalRateCertificate'], names),
    ('P5ERegressionAudit.lean', ['OddPiPowers', 'OddPiPowers.Vendor.PNT.Consequences'], regression),
]:
    text = 'module\n\n' + '\n'.join('import ' + s for s in imports) + '\n\n'
    text += '\n'.join('#print axioms ' + n for n in values) + '\n'
    (project / file).write_text(text, encoding='utf-8')
(project / 'logs/p5e-audit-expected.json').write_text(json.dumps(
    dict(new=names, regression=regression, source_sha256=hashes), indent=2), encoding='utf-8')
print(f'Prepared {len(names)} new and {len(regression)} regression checks.')
