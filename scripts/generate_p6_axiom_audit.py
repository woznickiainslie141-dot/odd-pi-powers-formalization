"""Freeze the exact complete P6 closure and prepare kernel axiom audits.

Does not compile. Run only after all sources/root imports are final and no
compiler or generator is active. Historical private helpers are covered by
the transitive closure of the public declarations that use them.
"""
from pathlib import Path
import hashlib,json,re

root=Path(__file__).resolve().parents[1]
project=root/'formalization/OddPiPowers'
logs=project/'logs'
prior=json.loads((logs/'p6b-guarded-library-build-state.json').read_text())
assert prior['status']=='completed' and prior['final_root_validated']
oldmods={r['module'] for r in prior['completed'] if r['module']!='OddPiPowers'}
visited=set();ordered=[]
def source(name):return project/(name.replace('.','/')+'.lean')
def visit(name):
    if name in visited:return
    visited.add(name)
    s=source(name).read_text(encoding='utf-8')
    for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',s,re.M):
        for dep in line.split():
            if dep=='OddPiPowers' or dep.startswith('OddPiPowers.'):visit(dep)
    ordered.append(name)
visit('OddPiPowers')
assert oldmods<=visited
newmods=[n for n in ordered if n not in oldmods and n!='OddPiPowers']
names=[];hashes={}
for mod in newmods:
    p=source(mod)
    hashes[str(p.relative_to(project))]=hashlib.sha256(p.read_bytes()).hexdigest()
    stack=[]
    for line in p.read_text(encoding='utf-8-sig').splitlines():
        ns=re.match(r'^namespace (\S+)',line)
        end=re.match(r'^end (\S+)',line)
        decl=re.match(r'^(?:noncomputable )?(def|theorem|lemma|abbrev|structure) ([\w.\']+)',line)
        if ns:stack.append(ns.group(1))
        elif end:assert stack.pop()==end.group(1),(p,line)
        elif decl:names.append('.'.join([*stack,decl.group(2)]))
    assert not stack,p
assert len(names)==len(set(names)) and newmods
previous=json.loads((logs/'p6b-audit-expected.json').read_text())
regression=previous['regression']+previous['new']
assert len(regression)==len(set(regression))==602
assert not set(names)&set(regression)
oldroot=(logs/'p6b-accepted-root.lean.txt').read_text(encoding='utf-8')
oldimports=[]
for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',oldroot,re.M):oldimports+=line.split()
oldimports=list(dict.fromkeys(oldimports+['OddPiPowers.Vendor.PNT.Consequences']))
for filename,imports,values in [
    ('P6AxiomAudit.lean',['OddPiPowers.Transfer.TwelveLayerPiCube'],names),
    ('P6RegressionAudit.lean',oldimports,regression)]:
    body='module\n\n'+'\n'.join('import '+x for x in imports)+'\n\n'
    body+='\n'.join('#print axioms '+x for x in values)+'\n'
    if filename=='P6AxiomAudit.lean':
        body+='\n'+'\n'.join('#check '+x for x in [
            'OddPiPowers.p6TwelveLayer_actualFamily',
            'OddPiPowers.pi_cube_exponentUpperBound_42170551935_div_35026168',
            'OddPiPowers.pi_cube_exponentUpperBound_lt_1203973_div_1000',
            'OddPiPowers.pi_cube_not_liouvilleWith_1203973_div_1000'])+'\n'
    (project/filename).write_text(body,encoding='utf-8')
(logs/'p6-audit-expected.json').write_text(json.dumps(dict(
    new=names,regression=regression,new_modules=newmods,source_sha256=hashes,
    library_plan=ordered,baseline='p6b-guarded-library-build-state.json'),indent=2),encoding='utf-8')
print(f'Prepared {len(newmods)} new modules; {len(names)} new and {len(regression)} regression declarations.')
