"""Emit the exact thirty-block arithmetic assembly (no compiler).

Run only while no proof compiler/generator is active. Imported lower-bound
theorems must each subsequently pass their bounded kernel checks.
"""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[1]
project=root/'formalization/OddPiPowers'
data=json.loads((project/'logs/p6-period-prefix-candidate.json').read_text())
scale=data['scale']
assert scale==10**14 and data['periods']==32
out=project/'OddPiPowers/Arithmetic/P6PeriodAggregate.lean'
imports=['OddPiPowers.Arithmetic.PeriodPrefixSum','OddPiPowers.Arithmetic.PeriodTailAggregate']
imports += [f'OddPiPowers.Arithmetic.P6Period{kind}{i:02d}' for kind in ['Prefix','Tail'] for i in range(30)]
lines=['module','']+['public import '+x for x in imports]+['',
    '/-! Assembly of exact finite prefix and finite tail certificates. -/','',
    '@[expose] public section','namespace OddPiPowers.PrimeRates','',
    'theorem p6_prefix_floor_lower :',
    f'    ({data["total_numerator"]} : ℝ) / {scale} ≤ selectedUnshrunkRate 32 := by',
    '  rw [← selected_periodPrefixLabels_actual_sum]',
    '  unfold selectedCells',
    '  simp only [twelveLayerCellTable, List.filter_append, periodPrefixLabels_append,',
    '    List.map_append, List.sum_append]']
# Sum all the inequalities first; linarith does not unfold the large cell lists.
for i in range(30):lines += [f'  have h{i} := p6PeriodPrefix{i:02d}_lower']
lines += ['  linarith','', 'theorem p6_tail_floor_lower :',
    f'    ({data["tail_numerator"]} : ℝ) / {scale} ≤',
    '      (selectedCells.map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by',
    '  unfold selectedCells',
    '  simp only [twelveLayerCellTable, List.filter_append, List.map_append, List.sum_append]']
for i in range(30):lines += [f'  have h{i} := p6PeriodTail{i:02d}_lower']
lines += ['  linarith','', 'end OddPiPowers.PrimeRates','']
out.write_text('\n'.join(lines),encoding='utf-8')
print(out)
