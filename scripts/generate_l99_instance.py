"""Generate independent L=99 candidate modules from accepted proof templates.

This program is not a proof oracle and never launches a compiler. All finite
claims still require ordinary kernel checking through bounded_lean.py.
No accepted mathematical source is overwritten.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, re

ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/'formalization/OddPiPowers'
SRC=PROJECT/'OddPiPowers'
OUT=SRC/'L99'
L,J,W,M,SCALE,CHUNK=99,28,16,43,4,20

def write(rel,text):
    if 'Validity' in rel or '/L99PeriodPrefix' in rel or '/L99PeriodTail' in rel or rel.endswith('/CellProbe.lean'):
        text=re.sub(r'\bby decide(?!\s*\+kernel)', 'by decide +kernel', text)
    p=OUT/rel;p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(text,encoding='utf-8')

TEMPLATES=[
 'Arithmetic/TwelveLayerCellSoundness','Arithmetic/TwelveLayerCellOrder',
 'Arithmetic/TwelveLayerCost','Arithmetic/TwelveLayerCertifiedBound',
 'Arithmetic/CellPrimeWindows','Arithmetic/ShrunkenCellWindows',
 'Arithmetic/PeriodWindowFamily','Arithmetic/CellWindowAggregate',
 'Arithmetic/PeriodFloorCertificate','Arithmetic/PeriodFloorBlock',
 'Arithmetic/PeriodPrefixSum','Arithmetic/PeriodTailFloor',
 'Arithmetic/PeriodTailAggregate','Arithmetic/TwelveLayerDivisorCertificate',
 'Construction/ScaledTwelveLayerFamily','Analysis/TwelveLayerActualRates',
 'Analysis/CentralNumericBounds',
]
MODULE_MAP={('OddPiPowers.'+s.replace('/','.')):
            ('OddPiPowers.L99.'+s.replace('/','.').replace('Twelve','TwentyEight'))
            for s in TEMPLATES}
for name in ['TwelveLayerCellChunks','TwelveLayerCellDefs','TwelveLayerCells','ScaledPrimeRates']:
    MODULE_MAP['OddPiPowers.Arithmetic.'+name]='OddPiPowers.L99.Arithmetic.'+name.replace('Twelve','TwentyEight')

def adapt(text,extra=None):
    for a,b in MODULE_MAP.items():text=text.replace(a,b)
    text=text.replace('namespace OddPiPowers','namespace OddPiPowers.L99')
    text=text.replace('end OddPiPowers','end OddPiPowers.L99')
    text=text.replace('Twelve','TwentyEight').replace('twelve','twentyEight')
    text=text.replace('eleven','twentySeven').replace('fin24','fin56')
    # Shape dimensions only. Certificate literals are generated independently.
    values={69:99,70:100,12:28,24:56,23:55,46:44,6:16,17:43,11:27,1180:3004}
    if extra:values.update(extra)
    text=re.sub(r'\b(?:'+ '|'.join(map(str,values))+r')\b',lambda m:str(values[int(m[0])]),text)
    if 'namespace OddPiPowers.L99.PrimeRates' in text:
        text=text.replace('namespace OddPiPowers.L99.PrimeRates',
                          'namespace OddPiPowers.L99.PrimeRates\n\nopen OddPiPowers.PrimeRates')
    return text

def cells():
    slopes=list(range(J))+list(range(L-J+1,L+1))
    differences={b-a for a in slopes for b in slopes if a<b}
    cuts=sorted({F(k,d) for d in differences for k in range(d+1)})
    assert len(cuts)-1==3004
    rows=[]
    for a,b in zip(cuts,cuts[1:]):
        z=(a+b)/2
        floors=[(s*z).numerator//(s*z).denominator for s in slopes]
        endpoints=[s*z-f for s,f in zip(slopes,floors)]
        assert len(set(endpoints))==2*J
        order=sorted(range(2*J),key=lambda h:endpoints[h])
        ranks=[order.index(h) for h in range(2*J)]
        def cost(q,point=False):
            result=0
            for j in range(J):
                ra,rb=ranks[j],ranks[2*J-1-j]
                if point:
                    rq=ranks[q]
                    v=(rb<rq<ra) if rb<ra else (rq<ra or rb<rq)
                else:v=(rb<=q<ra) if rb<ra else (q<ra or rb<=q)
                result+=(W if j==0 else 1)*v
            return result
        value=min(cost(q) for q in range(2*J))
        assert min(cost(q,True) for q in range(2*J))>=value
        row=dict(leftNumerator=a.numerator,leftDenominator=a.denominator,
                 rightNumerator=b.numerator,rightDenominator=b.denominator,
                 rankCode=sum(r*(2*J)**i for i,r in enumerate(ranks)),
                 orderCode=sum(h*(2*J)**r for r,h in enumerate(order)),
                 floorCode=sum(f*(L+1)**i for i,f in enumerate(floors)),value=value)
        rows.append(row)
    return rows

def literal(row):return '{ '+', '.join(f'{k} := {v}' for k,v in row.items())+' }'

def generate_cells(rows):
    chunks=[rows[i:i+CHUNK] for i in range(0,len(rows),CHUNK)]
    original=(SRC/'Arithmetic/TwelveLayerCellChunks.lean').read_text(encoding='utf-8')
    header=original[:original.index('def twelveCellRawDataRows0')]
    data=adapt(header)
    for i,chunk in enumerate(chunks):
        data+=f'def twentyEightCellRawDataRows{i} : List TwentyEightCellRawData := [\n'
        data+=',\n'.join('  '+literal(row) for row in chunk)+'\n]\n\n'
    data+='end OddPiPowers.L99\nend\n'
    write('Arithmetic/TwentyEightLayerCellChunks.lean',data)
    old=(SRC/'Arithmetic/TwelveLayerCellDefs.lean').read_text(encoding='utf-8')
    start=old.index('def twelveLayerCellChunk0')
    end=old.index('def twelveRank (')
    defs=''
    for i in range(len(chunks)):
        defs+=f'def twelveLayerCellChunk{i} : List TwelveCellCertificate :=\n  (twelveCellRawDataRows{i}).map twelveCellCertificateOfRaw\n\n'
    defs+='def twelveLayerCellTable : List TwelveCellCertificate :=\n'
    defs+=' ++\n'.join(f'  twelveLayerCellChunk{i}' for i in range(len(chunks)))+'\n\n'
    write('Arithmetic/TwentyEightLayerCellDefs.lean',adapt(old[:start]+defs+old[end:]))
    for rel in TEMPLATES:
        text=(SRC/(rel+'.lean')).read_text(encoding='utf-8')
        if rel.endswith('TwelveLayerCertifiedBound'):
            text=text[:text.index('theorem twelveLayerLowerBound_nontrivial')]+ 'end OddPiPowers\nend\n'
        if rel.endswith('ScaledTwelveLayerFamily'):
            text=text.replace('public import OddPiPowers.Arithmetic.TwelveLayerFamily',
                 'public import OddPiPowers.Arithmetic.TwelveLayerCellDefs\npublic import OddPiPowers.Arithmetic.CertifiedPrimeDivisor')
            text=adapt(text,{10:26})
        elif rel.endswith('CentralNumericBounds'):
            text=adapt(text,{8192:4096,13:12})
        elif rel.endswith('TwelveLayerActualRates'):
            text=text.replace('(347 / 23)','(389 / QDENMARK)')
            text=adapt(text,{67:97}).replace('QDENMARK','11')
        else:text=adapt(text)
        write(rel.replace('Twelve','TwentyEight')+'.lean',text)
    # Only the shape-specific theorem is duplicated. Generic scaling results
    # and the actual-divisor/PNT theorem remain accepted imports.
    old=(SRC/'Arithmetic/ScaledPrimeRates.lean').read_text(encoding='utf-8')
    theorem=old[old.index('theorem twelveLayer_scaled_actualDivisor_eventually_exp_lower'):]
    scaled='module\n\npublic import OddPiPowers.Arithmetic.ScaledPrimeRates\n'
    scaled+='public import OddPiPowers.L99.Arithmetic.CellPrimeWindows\n\n'
    scaled+='@[expose] public section\nopen scoped BigOperators Topology\n'
    scaled+='namespace OddPiPowers\n'+theorem
    # End in the source was OddPiPowers.PrimeRates, so supply its matching namespace.
    scaled=scaled.replace('namespace OddPiPowers\ntheorem','namespace OddPiPowers.PrimeRates\ntheorem')
    scaled=adapt(scaled).replace(
        'public import OddPiPowers.L99.Arithmetic.ScaledPrimeRates',
        'public import OddPiPowers.Arithmetic.ScaledPrimeRates')
    write('Arithmetic/ScaledPrimeRates.lean',scaled)
    for i,chunk in enumerate(chunks):
        lines=['module','public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellDefs',
               '@[expose] public section','namespace OddPiPowers.L99',
               'set_option maxRecDepth 20000','set_option maxHeartbeats 2000000','']
        for n,row in enumerate(chunk,i*CHUNK):
            lines.extend([f'theorem twentyEightCellLiteral_valid_{n} :',
              f'    ({literal(row)} : TwentyEightCellCertificate).Valid := by decide',''])
        lines.extend([f'theorem twentyEightCellsChunk{i}_valid :',
          f'    twentyEightLayerCellChunk{i}.all (fun c => c.Valid) = true := by',
          '  change (['])
        lines.extend('    ('+literal(row)+' : TwentyEightCellCertificate)'+(',' if j+1<len(chunk) else '')
                     for j,row in enumerate(chunk))
        lines.extend(['  ] : List TwentyEightCellCertificate).all (fun c => c.Valid) = true',
          '  exact '+' '.join(f'twentyEightCell_all_cons twentyEightCellLiteral_valid_{n} ('
                             for n in range(i*CHUNK,i*CHUNK+len(chunk)))+'(by rfl)'+')'*len(chunk),
          '', 'end OddPiPowers.L99','end',''])
        write(f'Arithmetic/TwentyEightLayerValidity{i:03}.lean','\n'.join(lines))
    imports=''.join(f'public import OddPiPowers.L99.Arithmetic.TwentyEightLayerValidity{i:03}\n'
                    for i in range(len(chunks)))
    positive=sum(row['value']>0 for row in rows)
    assembly='module\npublic import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellSoundness\n'+imports
    assembly+='@[expose] public section\nnamespace OddPiPowers.L99\nset_option maxRecDepth 20000\nset_option maxHeartbeats 2000000\n\n'
    assembly+='theorem twentyEightLayerCellTable_length : twentyEightLayerCellTable.length = 3004 := by decide\n\n'
    assembly+=f'theorem twentyEightLayerCellTable_positive_count :\n    (twentyEightLayerCellTable.filter (fun c => 0 < c.value)).length = {positive} := by decide\n\n'
    assembly+='theorem twentyEightLayerCellTable_all_valid :\n    ∀ c ∈ twentyEightLayerCellTable, c.Valid := by\n'
    assembly+='  have hall : twentyEightLayerCellTable.all (fun c => c.Valid) = true := by\n'
    assembly+='    simp only [twentyEightLayerCellTable, List.all_append,\n'
    assembly+=',\n'.join(f'      twentyEightCellsChunk{i}_valid' for i in range(len(chunks)))+', Bool.and_true]\n'
    assembly+='  intro c hc\n  exact of_decide_eq_true (List.all_eq_true.mp hall c hc)\n\nend OddPiPowers.L99\nend\n'
    write('Arithmetic/TwentyEightLayerCells.lean',assembly)
    # One literal for the first feasibility probe, independent of all validity chunks.
    write('Arithmetic/CellProbe.lean','\n'.join([
      'module','public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellDefs',
      '@[expose] public section','namespace OddPiPowers.L99',
      'set_option maxRecDepth 20000','set_option maxHeartbeats 2000000',
      f'theorem cellProbe : ({literal(rows[1])} : TwentyEightCellCertificate).Valid := by decide',
      '#print axioms cellProbe','end OddPiPowers.L99','']))
    report=dict(status='generated candidates; NOT Lean-accepted',L=L,layers=J,
      base_weights=[W]+[1]*(J-1),scale=SCALE,m=M*SCALE-1,cells=len(rows),
      positive_cells=positive,chunks=len(chunks),chunk_size=CHUNK,
      candidate_module_count=len(list(OUT.rglob('*.lean'))))
    (PROJECT/'logs/l99-generation-candidate.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

def generate_rates(rows):
    """Finite rational candidates; no Arb values enter any Lean proposition."""
    chunks=[rows[i:i+CHUNK] for i in range(0,len(rows),CHUNK)]
    scale,periods,K=10**14,32,10**6
    prefix_sums=[];tail_sums=[]
    for idx,chunk in enumerate(chunks):
        selected=[c for c in chunk if 0<c['value']<=M and c['leftNumerator']>0
                  and c['leftDenominator']<=L*c['leftNumerator']]
        floors=[];tails=[]
        for c in selected:
            A,C,B,D,w=(c[k] for k in ['leftNumerator','leftDenominator','rightNumerator','rightDenominator','value'])
            for r in range(periods):
                q=F(w*(B*C-A*D),L*(r*C+A)*(r*D+B))
                floors.append(q.numerator*scale//q.denominator)
            a,b=F(A,C),F(B,D)
            x,y=(b-a)/(periods+a),(b-a)/(K+a)
            gap=lambda r:1/(r+a)-1/(r+b)
            q=F(w,L)*(x-x*x/2-y+(gap(periods)-gap(K))/2)
            assert q>0
            tails.append(q.numerator*scale//q.denominator)
        for kind,values in [('Prefix',floors),('Tail',tails)]:
            tag=f'{idx:03}';stem=f'L99Period{kind}{tag}';name=f'l99Period{kind}{tag}'
            dependency='PeriodFloorBlock' if kind=='Prefix' else 'PeriodTailFloor'
            lines=['module',f'public import OddPiPowers.L99.Arithmetic.{dependency}',
              'public import OddPiPowers.L99.Arithmetic.CellWindowAggregate',
              '@[expose] public section','namespace OddPiPowers.L99.PrimeRates',
              'open OddPiPowers.PrimeRates','set_option maxRecDepth 20000',
              'set_option maxHeartbeats 2000000','',f'def {name}Floors : List ℕ := [']
            for j in range(0,len(values),16):
                lines.append('  '+', '.join(map(str,values[j:j+16]))+(',' if j+16<len(values) else ''))
            lines+= [']','']
            cell_list=f'(twentyEightLayerCellChunk{idx}.filter selectedCellPredicate)'
            if kind=='Prefix':
                lines += [f'theorem {name}_checked :',
                  f'    periodBlockCheck {scale} (periodPrefixLabels {periods} {cell_list})',
                  f'      {name}Floors = true := by decide','',
                  f'theorem {name}_sum : {name}Floors.sum = {sum(values)} := by decide','',
                  f'theorem {name}_lower : ({sum(values)} : ℝ) / {scale} ≤',
                  f'    ((periodPrefixLabels {periods} {cell_list}).map periodLabelActual).sum := by',
                  f'  have h := periodBlockCheck_sound {scale} _ _ {name}_checked',
                  f'  simpa only [{name}_sum, Nat.cast_ofNat] using h','']
            else:
                lines += [f'theorem {name}_checked :',
                  f'    tailBlockCheck {scale} {periods} {K} {cell_list} {name}Floors = true := by decide','',
                  f'theorem {name}_sum : {name}Floors.sum = {sum(values)} := by decide','',
                  f'theorem {name}_lower : ({sum(values)} : ℝ) / {scale} ≤',
                  f'    ({cell_list}.map (fun c => (periodTailRational {periods} {K} c : ℝ))).sum := by',
                  f'  have h := tailBlockCheck_sound {scale} {periods} {K} _ _ {name}_checked',
                  f'  simpa only [{name}_sum, Nat.cast_ofNat] using h','']
            lines += ['end OddPiPowers.L99.PrimeRates','']
            write('Arithmetic/'+stem+'.lean','\n'.join(lines))
        prefix_sums.append(sum(floors));tail_sums.append(sum(tails))
    assembly=['module','public import OddPiPowers.L99.Arithmetic.PeriodPrefixSum',
              'public import OddPiPowers.L99.Arithmetic.PeriodTailAggregate']
    for kind in ['Prefix','Tail']:
        assembly.extend(f'public import OddPiPowers.L99.Arithmetic.L99Period{kind}{idx:03}'
                        for idx in range(len(chunks)))
    assembly+=['@[expose] public section','namespace OddPiPowers.L99.PrimeRates',
               'open OddPiPowers.PrimeRates','set_option maxRecDepth 20000',
               'set_option maxHeartbeats 4000000','']
    for kind,values in [('Prefix',prefix_sums),('Tail',tail_sums)]:
        name='l99_'+kind.lower()+'_floor_lower'
        rhs=f'selectedUnshrunkRate {periods}' if kind=='Prefix' else f'selectedTailRationalSum {periods} {K}'
        assembly += [f'theorem {name} : ({sum(values)} : ℝ) / {scale} ≤ {rhs} := by']
        if kind=='Prefix':assembly+=['  rw [← selected_periodPrefixLabels_actual_sum]','  unfold selectedCells']
        else:assembly+=['  unfold selectedTailRationalSum selectedCells']
        assembly+=['  simp only [twentyEightLayerCellTable, List.filter_append, periodPrefixLabels_append,',
                   '    List.map_append, List.sum_append]']
        assembly.extend(f'  have h{idx} := l99Period{kind}{idx:03}_lower' for idx in range(len(chunks)))
        assembly+=['  linarith','']
    assembly+=['end OddPiPowers.L99.PrimeRates','']
    write('Arithmetic/L99PeriodAggregate.lean','\n'.join(assembly))
    gamma=F(5523626,100000)
    shrink=2*F(L)**2*F(1,10**24)*K*M*len(rows)/L
    finite=F(sum(prefix_sums)+sum(tail_sums),scale)-shrink
    assert gamma/SCALE<finite, (gamma/SCALE,finite)
    sharp=f'''module
public import OddPiPowers.L99.Arithmetic.L99PeriodAggregate
public import OddPiPowers.L99.Arithmetic.TwentyEightLayerDivisorCertificate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open Filter
open scoped Topology

theorem l99_finite_window_rate_lower :
    ({gamma.numerator} / {gamma.denominator*SCALE} : ℝ) ≤
      periodWindowRate {K} selectedCellSet selectedCellTemplate := by
  have ht := selectedTemplateRate_ge_prefix_add_tail {periods} {K} (by norm_num) (by norm_num)
    ({sum(prefix_sums)} / {scale}) ({sum(tail_sums)} / {scale})
    l99_prefix_floor_lower l99_tail_floor_lower
  apply le_trans _ ht
  norm_num [cellShrinkEpsilon]

theorem l99_actualDivisor_eventually_exp_lower {{ε : ℝ}} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp ((({gamma.numerator} / {gamma.denominator} : ℝ) - ε) * ((99 * N : ℕ) : ℝ)) ≤
        ((scaledTwentyEightLayerActualFamily 4 (by norm_num) N).actualAuxiliaryPrimeDivisor : ℝ) := by
  apply twentyEightLayer_actualDivisor_of_finite_rate 4 (by norm_num) {K}
    ({gamma.numerator} / {gamma.denominator}) _ hε
  have ht := l99_finite_window_rate_lower
  norm_num only [Nat.cast_ofNat]
  linarith

end OddPiPowers.L99.PrimeRates
'''
    write('Arithmetic/L99SharpDivisorRate.lean',sharp)
    def lean(q):return f'({q.numerator} / {q.denominator})'
    def series(x):
        r=(x-1)/(x+1)
        return 2*sum((r**(2*i+1)/F(2*i+1) for i in range(10)),F(0))
    def floorq(x,scale):return F(x.numerator*scale//x.denominator,scale)
    Y=F(1801,20);lowers=[]
    for j in range(J):
        c=F(L-2*j,L);z=(Y*Y+c*c/4)/4096
        a,b=floorq(series(z),10**12),floorq(series(1/c),10**12)
        lower=c/2*(12*F(6931471803,10**10)+a)+c*b+2*Y*(c/(2*Y)-(c/(2*Y))**3/3)
        q=floorq(lower,10**10);lowers.append(q)
        lines=['module','public import OddPiPowers.L99.Analysis.CentralNumericBounds',
               '@[expose] public section','namespace OddPiPowers.L99',
               'set_option maxRecDepth 10000','set_option maxHeartbeats 1000000','',
          f'theorem l99CentralInterval{j:02}_lower : ({lean(q)} : ℝ) ≤',
          f'    centralIntervalRate {lean(c)} (1801 / 20) := by',
          f'  have haQ : ({lean(a)} : ℚ) ≤ logSeries {lean(z)} 10 := by',
          '    norm_num [logSeries, Finset.sum_range_succ]',
          f'  have hbQ : ({lean(b)} : ℚ) ≤ logSeries {lean(1/c)} 10 := by',
          '    norm_num [logSeries, Finset.sum_range_succ]',
          f'  have ha := (logSeries_bounds {lean(z)} (by norm_num) 10).1',
          f'  have hb := (logSeries_bounds {lean(1/c)} (by norm_num) 10).1',
          f'  have haQR : (({lean(a)} : ℚ) : ℝ) ≤ (logSeries {lean(z)} 10 : ℝ) := Rat.cast_le.mpr haQ',
          f'  have hbQR : (({lean(b)} : ℚ) : ℝ) ≤ (logSeries {lean(1/c)} 10 : ℝ) := Rat.cast_le.mpr hbQ',
          '  have haR := haQR.trans ha','  have hbR := hbQR.trans hb',
          f'  have ht := centralIntervalRate_from_logs {lean(c)} (1801 / 20) {lean(a)} {lean(b)}',
          '    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)',
          '    (by norm_num at hbR ⊢ <;> exact hbR)',
          f'  have hq : ({lean(q)} : ℚ) ≤ centralRationalLower {lean(c)} (1801 / 20) {lean(a)} {lean(b)} := by',
          '    norm_num [centralRationalLower]',
          f'  have hqR : (({lean(q)} : ℚ) : ℝ) ≤ (centralRationalLower {lean(c)} (1801 / 20) {lean(a)} {lean(b)} : ℝ) := Rat.cast_le.mpr hq',
          '  have hfinal := hqR.trans ht','  norm_num at hfinal ⊢','  exact hfinal','',
          'end OddPiPowers.L99','']
        write(f'Analysis/L99CentralCertificate{j:02}.lean','\n'.join(lines))
    total=SCALE*(W*lowers[0]+sum(lowers[1:],F(0)))
    d0,g0=F(48945865,100000),F(26904882,100000)
    assert d0<total-F(314159265358979323847,10**20)/2*Y-(M*SCALE-1)
    numerical=['module','public import OddPiPowers.L99.Analysis.TwentyEightLayerActualRates']
    numerical += [f'public import OddPiPowers.L99.Analysis.L99CentralCertificate{j:02}' for j in range(J)]
    numerical += ['public import Mathlib.Analysis.Real.Pi.Bounds','public import Mathlib.Analysis.Complex.ExponentialBounds',
      'public import Mathlib.Tactic.Linarith','public import Mathlib.Tactic.NormNum',
      '@[expose] public section','namespace OddPiPowers.L99','open scoped BigOperators','',
      f'theorem l99_scaled_central_sum_lower : ({lean(total)} : ℝ) ≤',
      '    ∑ a : Fin (43 * 4), centralIntervalRate',
      '      (((99 - 2 * scaledTwentyEightLayerOffset 4 a : ℕ) : ℝ) / 99) (1801 / 20) := by',
      '  rw [scaledTwentyEightLayer_central_sum 4 (by norm_num) (1801 / 20)]',
      '  norm_num [Fin.sum_univ_succ]']
    numerical += [f'  have h{j:02} := l99CentralInterval{j:02}_lower' for j in range(J)]
    numerical += ['  norm_num at '+' '.join(f'h{j:02}' for j in range(J)),'  linarith','',
      f'theorem l99_actualDecay_lower : ({lean(d0)} : ℝ) ≤',
      '    actualDecay 171 99 (scaledTwentyEightLayerOffset 4) (1801 / 20) := by',
      '  have hsum := l99_scaled_central_sum_lower','  have hpi := Real.pi_lt_d20',
      '  unfold actualDecay','  linarith','',
      f'theorem l99_actualGrowth_upper : actualGrowth 171 99 (scaledTwentyEightLayerOffset 4) ≤ ({lean(g0)} : ℝ) := by',
      '  have hl := Real.log_two_lt_d9','  have hshape := scaledTwentyEightLayer_shapeRelativeLength 4 (by norm_num)',
      '  unfold actualGrowth','  rw [hshape]','  norm_num at hl ⊢','  linarith','',
      'end OddPiPowers.L99','']
    write('Analysis/L99NumericalRates.lean','\n'.join(numerical))
    D,G=d0+gamma,g0-gamma;m=M*SCALE-1;E=m*(D+G)/(D-2*G)
    assert E<F('1107.93')
    final=f'''module
public import OddPiPowers.Analysis.ActualReducedFamily
public import OddPiPowers.L99.Analysis.L99NumericalRates
public import OddPiPowers.L99.Arithmetic.L99SharpDivisorRate
public import OddPiPowers.Transfer.AuxiliaryFamilyRates
public import OddPiPowers.Transfer.IrrationalityTransfer
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace OddPiPowers.L99
open Filter Polynomial
open scoped Topology

noncomputable def l99Rows : ℕ → Fin (171 + 1) → Polynomial GaussianInt :=
  actualReducedRows 171 99 (scaledTwentyEightLayerActualFamily 4 (by norm_num))

theorem l99_actualFamily : AuxiliaryFamily 171 99 {lean(D)} {lean(G)} l99Rows := by
  have hA : ∀ a : Fin (171 + 1), 2 * scaledTwentyEightLayerOffset 4 a < 99 := by
    intro a
    have ha := scaledTwentyEightLayerOffset_le_twentySeven 4 (by norm_num) a
    omega
  have hdiv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.exp (({lean(gamma)} - ε) * ((99 * N : ℕ) : ℝ)) ≤
        ((scaledTwentyEightLayerActualFamily 4 (by norm_num) N).actualAuxiliaryPrimeDivisor : ℝ) := by
    intro ε hε
    exact PrimeRates.l99_actualDivisor_eventually_exp_lower hε
  have hfamily := actual_reduced_auxiliaryFamily 171 99 (by norm_num)
    (scaledTwentyEightLayerOffset 4) hA (scaledTwentyEightLayerActualFamily 4 (by norm_num))
    (by intro N; rfl) (by intro N a; rfl) (1801 / 20) (by norm_num) {lean(gamma)} hdiv
  have hd : ({lean(D)} : ℝ) ≤ actualDecay 171 99 (scaledTwentyEightLayerOffset 4) (1801 / 20) + {lean(gamma)} := by
    have h := l99_actualDecay_lower
    linarith
  have hg : actualGrowth 171 99 (scaledTwentyEightLayerOffset 4) - {lean(gamma)} ≤ ({lean(G)} : ℝ) := by
    have h := l99_actualGrowth_upper
    linarith
  exact hfamily.weaken_rates hd hg

theorem pi_cube_exponentUpperBound_l99_exact :
    ExponentUpperBound (Real.pi ^ 3) {lean(E)} := by
  have ht := irrationality_transfer 171 99 3 {lean(D)} {lean(G)}
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    l99Rows l99_actualFamily
  convert ht using 1
  norm_num

theorem pi_cube_exponentUpperBound_lt_110793_div_100 :
    ∃ B : ℝ, B < 110793 / 100 ∧ ExponentUpperBound (Real.pi ^ 3) B :=
  ⟨{lean(E)}, by norm_num, pi_cube_exponentUpperBound_l99_exact⟩

theorem pi_cube_not_liouvilleWith_110793_div_100 :
    ¬ LiouvilleWith (110793 / 100) (Real.pi ^ 3) :=
  not_liouvilleWith_of_exponentUpperBound pi_cube_exponentUpperBound_l99_exact (by norm_num)

end OddPiPowers.L99
'''
    write('Transfer/PiCube.lean',final)
    report=dict(status='rational candidates; not yet compiled',Y=str(Y),gamma=str(gamma),
      finite_base_rate=float(finite),gamma_base_target=float(gamma/SCALE),
      prefix_numerator=sum(prefix_sums),tail_numerator=sum(tail_sums),scale=scale,
      D0=str(d0),G0=str(g0),D=str(D),G=str(G),E=str(E),E_decimal=float(E),
      central_sum_lower=str(total),modules=len(list(OUT.rglob('*.lean'))))
    (PROJECT/'logs/l99-rate-candidates.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

def bundle_candidates():
    """Co-locate five independent proof batches; proof bodies stay identical."""
    arithmetic=OUT/'Arithmetic'
    counts={}
    for prefix,namespace in [('TwentyEightLayerValidity','OddPiPowers.L99'),
                             ('L99PeriodPrefix','OddPiPowers.L99.PrimeRates'),
                             ('L99PeriodTail','OddPiPowers.L99.PrimeRates')]:
        parts=sorted(p for p in arithmetic.glob(prefix+'*.lean')
                     if re.fullmatch(re.escape(prefix)+r'\d+\.lean',p.name))
        assert len(parts)==151,(prefix,len(parts))
        bundled=[]
        for group in range((len(parts)+4)//5):
            sources=[p.read_text(encoding='utf-8') for p in parts[group*5:group*5+5]]
            marker='set_option maxHeartbeats 2000000\n\n'
            header=sources[0].split(marker,1)[0]+marker
            bodies=[s.split(marker,1)[1].split('\nend '+namespace,1)[0] for s in sources]
            text=header+'\n\n'.join(bodies)+'\n\nend '+namespace+'\n'
            if prefix=='TwentyEightLayerValidity':text+='end\n'
            name=f'{prefix}Bundle{group:03}'
            write('Arithmetic/'+name+'.lean',text)
            bundled.append('OddPiPowers.L99.Arithmetic.'+name)
        parent=arithmetic/('TwentyEightLayerCells.lean' if prefix=='TwentyEightLayerValidity' else 'L99PeriodAggregate.lean')
        text=parent.read_text(encoding='utf-8')
        pattern=r'^public import OddPiPowers\.L99\.Arithmetic\.'+re.escape(prefix)+r'\d+\n'
        matches=list(re.finditer(pattern,text,re.M));assert len(matches)==151
        first=matches[0].start()
        text=re.sub(pattern,'',text,flags=re.M)
        text=text[:first]+''.join('public import '+name+'\n' for name in bundled)+text[first:]
        parent.write_text(text,encoding='utf-8')
        for path in parts:
            assert path.resolve().is_relative_to(OUT.resolve())
            path.unlink() # Only freshly generated unaccepted leaf files are replaced by bundles.
        counts[prefix]=len(bundled)
    fix_cell_assembly()
    fix_period_assembly()
    print(json.dumps(dict(bundles=counts,new_source_modules=len(list(OUT.rglob('*.lean')))),indent=2))

def fix_cell_assembly():
    """Avoid whole-table reduction; reuse chunk decisions and split membership."""
    rows=cells();chunks=[rows[i:i+CHUNK] for i in range(0,len(rows),CHUNK)]
    stats=['module','public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellDefs',
           '@[expose] public section','namespace OddPiPowers.L99',
           'set_option maxRecDepth 20000','set_option maxHeartbeats 2000000','']
    attributes=['attribute [local irreducible] twentyEightLayerCellTable',
                'attribute [local irreducible] '+' '.join(f'twentyEightLayerCellChunk{i}' for i in range(len(chunks))),'']
    stats+=attributes
    stats += ['private theorem cell_length_append {xs ys : List TwentyEightCellCertificate} {a b : ℕ}',
      '    (hx : xs.length = a) (hy : ys.length = b) : (xs ++ ys).length = a + b := by',
      '  rw [List.length_append, hx, hy]','',
      'private theorem cell_positive_append {xs ys : List TwentyEightCellCertificate} {a b : ℕ}',
      '    (hx : (xs.filter (fun c => 0 < c.value)).length = a)',
      '    (hy : (ys.filter (fun c => 0 < c.value)).length = b) :',
      '    ((xs ++ ys).filter (fun c => 0 < c.value)).length = a + b := by',
      '  rw [List.filter_append, List.length_append, hx, hy]','']
    for i,part in enumerate(chunks):
        stats += [f'theorem twentyEightCellsChunk{i}_length :',
          f'    twentyEightLayerCellChunk{i}.length = {len(part)} := by decide +kernel',
          f'theorem twentyEightCellsChunk{i}_positive_count :',
          f'    (twentyEightLayerCellChunk{i}.filter (fun c => 0 < c.value)).length = {sum(c["value"]>0 for c in part)} := by decide +kernel','']
    for positive in [False,True]:
        suffix='positive_count' if positive else 'length'
        rhs=sum(c['value']>0 for c in rows) if positive else len(rows)
        term='(twentyEightLayerCellTable.filter (fun c => 0 < c.value)).length' if positive else 'twentyEightLayerCellTable.length'
        helper='cell_positive_append' if positive else 'cell_length_append'
        proof=f'twentyEightCellsChunk0_{suffix}'
        for i in range(1,len(chunks)):
            proof=f'{helper} ({proof}) twentyEightCellsChunk{i}_{suffix}'
        stats += [f'theorem twentyEightLayerCellTable_{suffix} : {term} = {rhs} := by',
                  '  unfold twentyEightLayerCellTable','  exact '+proof,'']
    stats += ['end OddPiPowers.L99','end','']
    write('Arithmetic/TwentyEightLayerCellStats.lean','\n'.join(stats))
    imports=['module','public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellSoundness',
             'public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellStats']
    imports += [f'public import OddPiPowers.L99.Arithmetic.TwentyEightLayerValidityBundle{i:03}'
                for i in range((len(chunks)+4)//5)]
    lines=imports+['@[expose] public section','namespace OddPiPowers.L99',
          'set_option maxRecDepth 20000','set_option maxHeartbeats 2000000','']+attributes+[
          'private theorem cell_all_valid_of_bool {xs : List TwentyEightCellCertificate}',
          '    (hx : xs.all (fun c => c.Valid) = true) : ∀ c ∈ xs, c.Valid := by',
          '  intro c hc','  exact of_decide_eq_true (List.all_eq_true.mp hx c hc)','',
          'private theorem cell_all_valid_append {xs ys : List TwentyEightCellCertificate}',
          '    (hx : ∀ c ∈ xs, c.Valid) (hy : ∀ c ∈ ys, c.Valid) :',
          '    ∀ c ∈ xs ++ ys, c.Valid := by',
          '  intro c hc','  rcases List.mem_append.mp hc with h | h',
          '  · exact hx c h','  · exact hy c h','',
          'theorem twentyEightLayerCellTable_all_valid :',
          '    ∀ c ∈ twentyEightLayerCellTable, c.Valid := by',
          '  unfold twentyEightLayerCellTable']
    proof='(cell_all_valid_of_bool twentyEightCellsChunk0_valid)'
    for i in range(1,len(chunks)):
        proof=f'(cell_all_valid_append {proof} (cell_all_valid_of_bool twentyEightCellsChunk{i}_valid))'
    lines+=['  exact '+proof]
    lines += ['','end OddPiPowers.L99','end','']
    write('Arithmetic/TwentyEightLayerCells.lean','\n'.join(lines))
    fix_cell_order(rows,chunks,attributes)
    print('Prepared small chunk statistics and structural all-valid assembly.')

def fix_cell_order(rows,chunks,attributes):
    old=adapt((SRC/'Arithmetic/TwelveLayerCellOrder.lean').read_text(encoding='utf-8'))
    tail=old[old.index('theorem twentyEightLayerCellTable_touching'):]
    header=old[:old.index('-- This checks endpoint equality only')]
    generic='''
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def ChainSummary (xs : List TwentyEightCellCertificate) (a b c d : ℕ) : Prop :=
  xs.IsChain twentyEightCellsNext ∧
  xs.head?.map (fun x => (x.leftNumerator, x.leftDenominator)) = some (a,b) ∧
  xs.getLast?.map (fun x => (x.rightNumerator, x.rightDenominator)) = some (c,d)

private instance (xs : List TwentyEightCellCertificate) (a b c d : ℕ) :
    Decidable (ChainSummary xs a b c d) := by unfold ChainSummary; infer_instance

private theorem option_pair_of_mem {o : Option TwentyEightCellCertificate}
    {f : TwentyEightCellCertificate → ℕ × ℕ} {p : ℕ × ℕ} {x : TwentyEightCellCertificate}
    (h : o.map f = some p) (hx : x ∈ o) : f x = p := by
  cases o with
  | none => simp at hx
  | some y =>
    have hxy : y = x := by simpa using hx
    subst y
    simpa using h

private theorem chain_summary_append {xs ys : List TwentyEightCellCertificate}
    {a b c d e f : ℕ} (hx : ChainSummary xs a b c d) (hy : ChainSummary ys c d e f) :
    ChainSummary (xs ++ ys) a b e f := by
  have hxs : xs ≠ [] := by intro h; simp [ChainSummary, h] at hx
  have hys : ys ≠ [] := by intro h; simp [ChainSummary, h] at hy
  refine ⟨hx.1.append hy.1 ?_, ?_, ?_⟩
  · intro x hxm y hym
    have hp := option_pair_of_mem hx.2.2 hxm
    have hq := option_pair_of_mem hy.2.1 hym
    exact ⟨(congrArg Prod.fst hp).trans (congrArg Prod.fst hq).symm,
      (congrArg Prod.snd hp).trans (congrArg Prod.snd hq).symm⟩
  · rw [List.head?_append_of_ne_nil _ hxs]
    exact hx.2.1
  · rw [List.getLast?_append_of_ne_nil _ hys]
    exact hy.2.2

'''
    lines=[header,generic,*attributes]
    for i,chunk in enumerate(chunks):
        first,last=chunk[0],chunk[-1]
        a,b=first['leftNumerator'],first['leftDenominator']
        c,d=last['rightNumerator'],last['rightDenominator']
        lines += [f'private theorem cell_chain_chunk_{i} : ChainSummary twentyEightLayerCellChunk{i} {a} {b} {c} {d} := by decide +kernel','']
    proof='cell_chain_chunk_0'
    for i in range(1,len(chunks)):proof=f'chain_summary_append ({proof}) cell_chain_chunk_{i}'
    lines+=['private theorem whole_chain_summary : ChainSummary twentyEightLayerCellTable 0 1 1 1 := by',
            '  unfold twentyEightLayerCellTable','  exact '+proof,'',
            'theorem twentyEightLayerCellTable_next : twentyEightLayerCellTable.IsChain twentyEightCellsNext :=',
            '  whole_chain_summary.1','',tail]
    write('Arithmetic/TwentyEightLayerCellOrder.lean','\n'.join(lines))

def fix_period_assembly():
    """Compose proved chunk bounds without expanding the real-valued table."""
    path=OUT/'Arithmetic/L99PeriodAggregate.lean'
    header=path.read_text(encoding='utf-8').split('@[expose]',1)[0]
    numbers={}
    for kind in ['Prefix','Tail']:
        entries={}
        for part in sorted((OUT/'Arithmetic').glob(f'L99Period{kind}Bundle*.lean')):
            text=part.read_text(encoding='utf-8')
            for idx,value in re.findall(rf'theorem l99Period{kind}(\d+)_lower : \((\d+) : ℝ\)',text):
                entries[int(idx)]=int(value)
        assert sorted(entries)==list(range(151)),(kind,len(entries))
        numbers[kind]=[entries[i] for i in range(151)]
    lines=[header,'@[expose] public section','namespace OddPiPowers.L99.PrimeRates',
      'open OddPiPowers.PrimeRates','set_option maxRecDepth 20000','set_option maxHeartbeats 4000000',
      'attribute [local irreducible] twentyEightLayerCellTable twentyEightCellCertificateOfRaw',
      'attribute [local irreducible] periodPrefixLabels periodLabelActual periodTailRational','',
      'private noncomputable def prefixFilteredRate (xs : List TwentyEightCellCertificate) : ℝ :=',
      '  ((periodPrefixLabels 32 (xs.filter selectedCellPredicate)).map periodLabelActual).sum','',
      'private noncomputable def tailFilteredRate (xs : List TwentyEightCellCertificate) : ℝ :=',
      '  ((xs.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum','']
    scale=10**14
    for kind,stem in [('Prefix','prefix'),('Tail','tail')]:
        function=stem+'FilteredRate'
        lines += [f'private theorem {stem}_filtered_append (xs ys : List TwentyEightCellCertificate) :',
          f'    {function} (xs ++ ys) = {function} xs + {function} ys := by',
          f'  simp only [{function}, List.filter_append, periodPrefixLabels_append, List.map_append, List.sum_append]','',
          f'private theorem {stem}_lower_append {{xs ys : List TwentyEightCellCertificate}} {{a b : ℕ}}',
          f'    (hx : (a : ℝ) / {scale} ≤ {function} xs)',
          f'    (hy : (b : ℝ) / {scale} ≤ {function} ys) :',
          f'    ((a + b : ℕ) : ℝ) / {scale} ≤ {function} (xs ++ ys) := by',
          f'  rw [{stem}_filtered_append, Nat.cast_add, add_div]',
          '  exact add_le_add hx hy','']
        for i,value in enumerate(numbers[kind]):
            lines += [f'private theorem {stem}_chunk_lower_{i} :',
              f'    ({value} : ℝ) / {scale} ≤ {function} twentyEightLayerCellChunk{i} := by',
              f'  simpa only [{function}] using l99Period{kind}{i:03}_lower','']
        proof=f'{stem}_chunk_lower_0'
        for i in range(1,151):proof=f'{stem}_lower_append ({proof}) {stem}_chunk_lower_{i}'
        total=sum(numbers[kind])
        lines += [f'private theorem {stem}_whole_lower :',
          f'    ({total} : ℝ) / {scale} ≤ {function} twentyEightLayerCellTable := by',
          '  unfold twentyEightLayerCellTable','  exact '+proof,'']
        target='selectedUnshrunkRate 32' if kind=='Prefix' else 'selectedTailRationalSum 32 1000000'
        lines += [f'theorem l99_{stem}_floor_lower : ({total} : ℝ) / {scale} ≤ {target} := by']
        if kind=='Prefix':
            lines += ['  have h := prefix_whole_lower',
              '  have heq : prefixFilteredRate twentyEightLayerCellTable = selectedUnshrunkRate 32 := by',
              '    simpa only [prefixFilteredRate, selectedCells] using (selected_periodPrefixLabels_actual_sum 32)',
              '  exact h.trans_eq heq','']
        else:
            lines += ['  simpa only [tailFilteredRate, selectedTailRationalSum, selectedCells] using tail_whole_lower','']
    lines += ['end OddPiPowers.L99.PrimeRates','']
    write('Arithmetic/L99PeriodAggregate.lean','\n'.join(lines))
    print('Prepared structural prefix/tail lower-bound assembly.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cells',action='store_true')
    parser.add_argument('--rates',action='store_true')
    parser.add_argument('--bundle',action='store_true')
    parser.add_argument('--assembly',action='store_true')
    parser.add_argument('--period-assembly',action='store_true')
    args=parser.parse_args()
    if args.cells:generate_cells(cells())
    elif args.rates:generate_rates(cells())
    elif args.bundle:bundle_candidates()
    elif args.assembly:fix_cell_assembly()
    elif args.period_assembly:fix_period_assembly()
    else:parser.error('Choose a generation or assembly phase.')

if __name__=='__main__':main()
