"""Prepare exact new and regression axiom name sets; never runs Lean."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent.parent
project = root / 'formalization/OddPiPowers'
files = ['HorizontalProduct', 'ActualHorizontalGeometry', 'ActualHorizontalTail',
         'HorizontalMajorant', 'HorizontalKernelBound', 'HorizontalKernelIntegrable',
         'TwelveLayerHorizontal']
names = []
hashes = {}
for filename in files:
    path = project / f'OddPiPowers/Analysis/{filename}.lean'
    hashes[str(path.relative_to(project))] = hashlib.sha256(path.read_bytes()).hexdigest()
    stack = []
    for line in path.read_text(encoding='utf-8').splitlines():
        ns = re.match(r'^namespace (\S+)', line)
        end = re.match(r'^end (\S+)', line)
        decl = re.match(r'^(?:noncomputable )?(?:def|theorem) ([\w.\']+)', line)
        if ns:
            stack.append(ns.group(1))
        elif end:
            assert stack.pop() == end.group(1), (path, line)
        elif decl:
            names.append('.'.join([*stack, decl.group(1)]))
    assert not stack, path
assert len(names) == len(set(names))
old = re.findall(r'^#print axioms (\S+)', (project / 'AxiomAudit.lean').read_text(encoding='utf-8'), re.M)
old += json.loads((project / 'logs/p4-audit-expected.json').read_text(encoding='utf-8'))
assert len(old) == len(set(old)) == 239
for file, imports, values in [
    ('P5AAxiomAudit.lean', ['OddPiPowers.Analysis.TwelveLayerHorizontal'], names),
    ('P5ARegressionAudit.lean', ['OddPiPowers', 'OddPiPowers.Vendor.PNT.Consequences'], old),
]:
    text = 'module\n\n' + '\n'.join('import ' + s for s in imports) + '\n\n'
    text += '\n'.join('#print axioms ' + n for n in values) + '\n'
    (project / file).write_text(text, encoding='utf-8')
(project / 'logs/p5a-audit-expected.json').write_text(json.dumps(
    dict(new=names, regression=old, source_sha256=hashes), indent=2), encoding='utf-8')
print(f'Prepared {len(names)} new and {len(old)} regression checks.')
