"""Prepare the exact first unconditional pi^3 instance audit; never compiles."""
from pathlib import Path
import hashlib,json,re

root=Path(__file__).resolve().parents[1]
project=root/'formalization/OddPiPowers'
files=['Analysis/'+x for x in ['SeriesCoefficientMajorant','BalancedSeriesFactors',
    'BalancedLocalHeight','BalancedValueHeight','PolynomialDiskHeight','BalancedHeightRate',
    'BalancedDiskHeight','BalancedAuxiliaryFamily','BalancedNumericCertificate']]
files+=['Construction/BalancedActualFamily','Construction/GaussianAuxiliaryRows',
        'Transfer/AuxiliaryFamilyRates','Transfer/BalancedPiCube']
names=[]; hashes={}
for filename in files:
    path=project/f'OddPiPowers/{filename}.lean'
    hashes[str(path.relative_to(project))]=hashlib.sha256(path.read_bytes()).hexdigest()
    stack=[]
    for line in path.read_text(encoding='utf-8').splitlines():
        ns=re.match(r'^namespace (\S+)',line)
        end=re.match(r'^end (\S+)',line)
        decl=re.match(r'^(?:noncomputable )?(def|theorem|lemma) ([\w.\']+)',line)
        if ns:stack.append(ns.group(1))
        elif end:assert stack.pop()==end.group(1),(path,line)
        elif decl:names.append('.'.join([*stack,decl.group(2)]))
    assert not stack,path
assert len(names)==len(set(names))==81
old=json.loads((project/'logs/p5e-audit-expected.json').read_text())
regression=old['regression']+old['new']
assert len(regression)==len(set(regression))==521
assert not set(names).intersection(regression)
for filename,imports,values in [
    ('P6BAxiomAudit.lean',['OddPiPowers.Transfer.BalancedPiCube'],names),
    ('P6BRegressionAudit.lean',['OddPiPowers','OddPiPowers.Vendor.PNT.Consequences'],regression)]:
    text='module\n\n'+'\n'.join('import '+s for s in imports)+'\n\n'
    text+='\n'.join('#print axioms '+n for n in values)+'\n'
    (project/filename).write_text(text,encoding='utf-8')
(project/'logs/p6b-audit-expected.json').write_text(json.dumps(
    dict(new=names,regression=regression,source_sha256=hashes),indent=2),encoding='utf-8')
print(f'Prepared {len(names)} new and {len(regression)} regression checks.')
