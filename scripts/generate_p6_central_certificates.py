"""Candidate rational log-series certificates. Does not launch Lean.

Execute only with no compiler/generator active. Every claim is an ordinary
kernel-checkable ground rational comparison, not a numerical oracle.
"""
from pathlib import Path
from fractions import Fraction as F
import json

root=Path(__file__).resolve().parents[1]
project=root/'formalization/OddPiPowers'
out=project/'OddPiPowers/Analysis'
Y=F(2113,20)
log2=F(6931471803,10**10)
def series(x,n=10):
    r=(x-1)/(x+1)
    return 2*sum((r**(2*i+1)/F(2*i+1) for i in range(n)),F(0))
def floorq(x,scale): return F((x.numerator*scale)//x.denominator,scale)
def lean(x):return f'({x.numerator} / {x.denominator})'
values=[]
for j,c in enumerate([F(1)]+[F(69-2*k,69) for k in range(1,12)]):
    z=(Y*Y+c*c/4)/8192
    a,b=floorq(series(z),10**12),floorq(series(1/c),10**12)
    lower=c/2*(13*log2+a)+c*b+2*Y*(c/(2*Y)-(c/(2*Y))**3/3)
    q=floorq(lower,10**10)
    assert q<=lower
    tag=f'{j:02d}'
    lines=['module','','public import OddPiPowers.Analysis.CentralNumericBounds','',
           '/-! Exact rational candidates, certified by finite-series inequalities. -/','',
           '@[expose] public section','namespace OddPiPowers',
           'set_option maxRecDepth 10000','set_option maxHeartbeats 1000000','',
           f'theorem p6CentralInterval{tag}_lower : ({lean(q)} : ℝ) ≤',
           f'    centralIntervalRate {lean(c)} (2113 / 20) := by',
           f'  have haQ : ({lean(a)} : ℚ) ≤ logSeries {lean(z)} 10 := by',
           '    norm_num [logSeries, Finset.sum_range_succ]',
           f'  have hbQ : ({lean(b)} : ℚ) ≤ logSeries {lean(1/c)} 10 := by',
           '    norm_num [logSeries, Finset.sum_range_succ]',
           f'  have ha := (logSeries_bounds {lean(z)} (by norm_num) 10).1',
           f'  have hb := (logSeries_bounds {lean(1/c)} (by norm_num) 10).1',
           f'  have haQR : (({lean(a)} : ℚ) : ℝ) ≤ (logSeries {lean(z)} 10 : ℝ) := Rat.cast_le.mpr haQ',
           f'  have hbQR : (({lean(b)} : ℚ) : ℝ) ≤ (logSeries {lean(1/c)} 10 : ℝ) := Rat.cast_le.mpr hbQ',
           '  have haR := haQR.trans ha',
           '  have hbR := hbQR.trans hb',
           f'  have ht := centralIntervalRate_from_logs {lean(c)} (2113 / 20) {lean(a)} {lean(b)}',
           '    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)',
           '    (by norm_num at hbR ⊢ <;> exact hbR)',
           f'  have hq : ({lean(q)} : ℚ) ≤ centralRationalLower {lean(c)} (2113 / 20) {lean(a)} {lean(b)} := by',
           '    norm_num [centralRationalLower]',
           f'  have hqR : (({lean(q)} : ℚ) : ℝ) ≤ (centralRationalLower {lean(c)} (2113 / 20) {lean(a)} {lean(b)} : ℝ) := Rat.cast_le.mpr hq',
           '  have hfinal := hqR.trans ht',
           '  norm_num at hfinal ⊢',
           '  exact hfinal','', 'end OddPiPowers','']
    (out/f'P6CentralCertificate{tag}.lean').write_text('\n'.join(lines),encoding='utf-8')
    values.append(dict(c=str(c),log_scaled_lower=str(a),log_reciprocal_lower=str(b),lower=str(q)))
total=11*(6*F(values[0]['lower'])+sum((F(x['lower']) for x in values[1:]),F(0)))
report=dict(status='candidate, NOT compiled or accepted',Y=str(Y),rows=values,
            central_sum_lower=str(total),
            D0_using_pi_d20=str(total-F(314159265358979323847,10**20)/2*Y-186))
(project/'logs/p6-central-candidate.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
print(json.dumps(report,indent=2))
