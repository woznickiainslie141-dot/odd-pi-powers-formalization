"""Generate candidate integer floor certificates from ACCEPTED Lean cell data.

No compiler is launched. Run only when no guarded compiler/generator is active.
The generated propositions still require ordinary kernel checking.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib, json, re

root = Path(__file__).resolve().parents[1]
project = root / 'formalization/OddPiPowers'
arithmetic = project / 'OddPiPowers/Arithmetic'
data = arithmetic / 'TwelveLayerCellChunks.lean'
text = data.read_text(encoding='utf-8')
scale, periods = 10**14, 32
chunks = []
totals = []
tail_totals = []
for idx in range(30):
    match = re.search(rf'def twelveCellRawDataRows{idx} : List TwelveCellRawData := \[(.*?)\n\]', text, re.S)
    assert match, idx
    cells = []
    floors = []
    for literal in re.findall(r'\{([^{}]+)\}', match.group(1)):
        c = {key: int(val) for key, val in re.findall(r'(\w+) := (\d+)', literal)}
        assert len(c) == 8
        A,C,B,D,w = (c[k] for k in ['leftNumerator','leftDenominator','rightNumerator','rightDenominator','value'])
        if not (0<w<=17 and A>0 and C<=69*A):
            continue
        assert C>0 and D>0 and A*D<B*C
        cells.append(c)
        for r in range(periods):
            q = F(w*(B*C-A*D), 69*(r*C+A)*(r*D+B))
            p = (scale*q.numerator)//q.denominator
            assert p*q.denominator <= scale*q.numerator
            floors.append(p)
    stem = f'P6PeriodPrefix{idx:02d}'
    name = f'p6PeriodPrefix{idx:02d}'
    lines = ['module', '', 'public import OddPiPowers.Arithmetic.PeriodFloorBlock',
             'public import OddPiPowers.Arithmetic.CellWindowAggregate', '',
             '/-! Candidate integer floors; all comparisons are checked by the kernel. -/', '',
             '@[expose] public section', 'namespace OddPiPowers.PrimeRates',
             'set_option maxRecDepth 10000', 'set_option maxHeartbeats 2000000', '',
             f'def {name}Floors : List ℕ := [']
    for j in range(0,len(floors),16):
        lines.append('  '+', '.join(map(str,floors[j:j+16]))+(',' if j+16<len(floors) else ''))
    lines += [']', '', f'theorem {name}_checked :',
              f'    periodBlockCheck {scale} (periodPrefixLabels {periods}',
              f'      (twelveLayerCellChunk{idx}.filter selectedCellPredicate)) {name}Floors = true := by decide', '',
              f'theorem {name}_sum : {name}Floors.sum = {sum(floors)} := by decide', '',
              f'theorem {name}_lower : ({sum(floors)} : ℝ) / {scale} ≤',
              f'    ((periodPrefixLabels {periods} (twelveLayerCellChunk{idx}.filter selectedCellPredicate)).map',
              '      periodLabelActual).sum := by',
              f'  have h := periodBlockCheck_sound {scale} _ _ {name}_checked',
              f'  simpa only [{name}_sum, Nat.cast_ofNat] using h', '', 'end OddPiPowers.PrimeRates', '']
    path = arithmetic / (stem+'.lean')
    path.write_text('\n'.join(lines), encoding='utf-8')
    tail_floors = []
    for c in cells:
        a,b = F(c['leftNumerator'],c['leftDenominator']), F(c['rightNumerator'],c['rightDenominator'])
        x,y = (b-a)/(periods+a), (b-a)/(10**6+a)
        gap = lambda r: 1/(r+a)-1/(r+b)
        q = F(c['value'],69)*(x-x*x/2-y+(gap(periods)-gap(10**6))/2)
        assert q>0
        p = (scale*q.numerator)//q.denominator
        assert F(p,scale)<=q
        tail_floors.append(p)
    tailname = f'p6PeriodTail{idx:02d}'
    tailsource = '\n'.join([
        'module', '', 'public import OddPiPowers.Arithmetic.PeriodTailFloor',
        'public import OddPiPowers.Arithmetic.CellWindowAggregate', '',
        '/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/', '',
        '@[expose] public section', 'namespace OddPiPowers.PrimeRates',
        'set_option maxRecDepth 10000', 'set_option maxHeartbeats 2000000', '',
        f'def {tailname}Floors : List ℕ := [',
        '  '+', '.join(map(str,tail_floors)), ']', '',
        f'theorem {tailname}_checked : tailBlockCheck {scale} {periods} 1000000',
        f'    (twelveLayerCellChunk{idx}.filter selectedCellPredicate) {tailname}Floors = true := by decide', '',
        f'theorem {tailname}_sum : {tailname}Floors.sum = {sum(tail_floors)} := by decide', '',
        f'theorem {tailname}_lower : ({sum(tail_floors)} : ℝ) / {scale} ≤',
        f'    ((twelveLayerCellChunk{idx}.filter selectedCellPredicate).map',
        '      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by',
        f'  have h := tailBlockCheck_sound {scale} 32 1000000 _ _ {tailname}_checked',
        f'  simpa only [{tailname}_sum, Nat.cast_ofNat] using h', '', 'end OddPiPowers.PrimeRates', ''])
    (arithmetic/f'P6PeriodTail{idx:02d}.lean').write_text(tailsource,encoding='utf-8')
    tail_totals.append(sum(tail_floors))
    totals.append(sum(floors))
    chunks.append(dict(module=stem,cells=len(cells),floors=len(floors),numerator=sum(floors),
                       source_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
report=dict(status='candidate, NOT compiled or accepted',periods=periods,scale=scale,
            accepted_data_source=str(data.relative_to(root)),
            accepted_data_sha256=hashlib.sha256(data.read_bytes()).hexdigest(),
            chunks=chunks,total_numerator=sum(totals),total_floor_rate=str(F(sum(totals),scale)),
            tail_numerator=sum(tail_totals),combined_floor_rate=str(F(sum(totals)+sum(tail_totals),scale)))
(project/'logs/p6-period-prefix-candidate.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k!='chunks'},indent=2))
