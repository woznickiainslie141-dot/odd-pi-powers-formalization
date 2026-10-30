from pathlib import Path
import re

repo = Path(__file__).resolve().parents[1]
data = repo / 'formalization' / 'OddPiPowers' / 'OddPiPowers' / 'Arithmetic' / 'TwelveLayerCellData.lean'
source = data.read_text(encoding='utf-8')
rows = []
for k in range(10):
    name = f'twelveRankValueRows{k}'
    match = re.search(rf'def {name} : List \(Nat × Nat\) := \[([\s\S]*?)\]', source)
    if not match:
        raise RuntimeError(f'missing {name}')
    rows.extend((int(a), int(v)) for a, v in re.findall(r'\((\d+),\s*(\d+)\)', match.group(1)))
if len(rows) != 1180:
    raise RuntimeError(f'expected 1180 cells, got {len(rows)}')
order_codes = []
for rank_code, _value in rows:
    ranks = [(rank_code // (24 ** i)) % 24 for i in range(24)]
    if sorted(ranks) != list(range(24)):
        raise RuntimeError('a candidate rank code is not a permutation')
    inverse = [ranks.index(r) for r in range(24)]
    order_codes.append(sum(endpoint * (24 ** r) for r, endpoint in enumerate(inverse)))
chunks = [order_codes[i:i+100] for i in range(0, len(order_codes), 100)]
lines = ['/- BEGIN generated order codes -/']
for k, chunk in enumerate(chunks):
    lines += [f'def twelveOrderCodeRows{k} : List Nat := [', '  ' + ', '.join(map(str, chunk)), ']']
lines += ['def twelveOrderCodeRows : List Nat :=']
lines += [f'  twelveOrderCodeRows{k}' + (' ++' if k + 1 < len(chunks) else '') for k in range(len(chunks))]
lines += ['/- END generated order codes -/']
block = '\n'.join(lines)
start = source.find('/- BEGIN generated order codes -/')
if start >= 0:
    end = source.index('/- END generated order codes -/', start) + len('/- END generated order codes -/')
    source = source[:start] + block + source[end:]
else:
    marker = '/- BEGIN generated floor codes -/'
    at = source.find(marker)
    if at < 0:
        raise RuntimeError('missing floor-code insertion marker')
    source = source[:at] + block + '\n\n' + source[at:]
data.write_text(source, encoding='utf-8')
print(f'cells={len(order_codes)}, chunks={len(chunks)}, first={order_codes[0]}')
