"""Write the new-declaration audit only; does not compile or evaluate proofs."""
from pathlib import Path
import json
import re

workspace=Path(__file__).resolve().parent.parent
project=workspace/'formalization/OddPiPowers'
files=['FinitePeriodKernel','PrimeWindowGeometry','FiniteWindowCover','PrimeWindowSums',
       'PrimeWindowDivisor','PrimeNumberRates','CellPrimeWindows','PrimeDivisorRates',
       'PrimeRateCalibration','TwelveLayerFamily','ActualPrimeDivisorRates','ScaledPrimeRates',
       'TwelveLayerPrimeRates']
names=['WeakPNT',"WeakPNT'","WeakPNT''",'chebyshev_asymptotic']
for file in files:
    text=(project/f'OddPiPowers/Arithmetic/{file}.lean').read_text(encoding='utf-8')
    namespace='OddPiPowers' if file=='TwelveLayerFamily' else 'OddPiPowers.PrimeRates'
    for name in re.findall(r'^(?:noncomputable )?(?:theorem|def)\s+([\w.\']+)',text,re.M):
        names.append(namespace+'.'+name)
assert len(names)==len(set(names))
(project/'P4AxiomAudit.lean').write_text('module\n\nimport OddPiPowers.Arithmetic.TwelveLayerPrimeRates\nimport OddPiPowers.Vendor.PNT.Consequences\n\n'+
    '\n'.join('#print axioms '+name for name in names)+'\n',encoding='utf-8')
(project/'logs/p4-audit-expected.json').write_text(json.dumps(names,indent=2),encoding='utf-8')
previous=re.findall(r'^#print axioms (\S+)',(project/'AxiomAudit.lean').read_text(encoding='utf-8'),re.M)
(project/'P4RegressionAudit.lean').write_text('module\n\nimport OddPiPowers\n\n'+
    '\n'.join('#print axioms '+name for name in previous)+'\n',encoding='utf-8')
print(f'Prepared {len(names)} P4 transitive axiom checks.')
