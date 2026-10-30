"""Emit ordinary Lean kernel proofs for exact literal rows; no external truth claims."""
from pathlib import Path
import argparse
import re

p=argparse.ArgumentParser()
p.add_argument('chunks',nargs='+',type=int)
a=p.parse_args()
base=Path(__file__).resolve().parents[1]/'formalization/OddPiPowers/OddPiPowers/Arithmetic'
data=(base/'TwelveLayerCellChunks.lean').read_text(encoding='utf-8')
rows=re.findall(r'\{ leftNumerator := \d+.*?value := \d+ \}',data)
assert len(rows)==1180,len(rows)
for chunk in a.chunks:
    assert 0<=chunk<30
    part=rows[40*chunk:min(40*(chunk+1),1180)]
    lines=['module','public import OddPiPowers.Arithmetic.TwelveLayerCellDefs',
           '@[expose] public section','namespace OddPiPowers',
           'set_option maxRecDepth 10000','set_option maxHeartbeats 1000000','']
    for j,row in enumerate(part,40*chunk):
        lines += [f'theorem twelveCellLiteral_valid_{j} :',
                  f'    ({row} : TwelveCellCertificate).Valid := by decide','']
    lines += [f'theorem twelveCellsChunk{chunk}_valid :',
              f'    twelveLayerCellChunk{chunk}.all (fun c => c.Valid) = true := by',
              '  change ([']
    lines += ['    ('+row+' : TwelveCellCertificate)'+(',' if j+1<len(part) else '')
              for j,row in enumerate(part)]
    lines += ['  ] : List TwelveCellCertificate).all (fun c => c.Valid) = true',
              '  exact '+' '.join(f'twelveCell_all_cons twelveCellLiteral_valid_{j} ('
                                  for j in range(40*chunk,40*chunk+len(part)))+
                       '(by rfl)'+')'*len(part),
              '', 'end OddPiPowers','end','']
    target=base/f'TwelveLayerValidity{chunk:02}.lean'
    target.write_text('\n'.join(lines),encoding='utf-8')
    print(target.name,len(part),'literal proofs')
