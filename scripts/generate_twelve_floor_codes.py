from fractions import Fraction
from pathlib import Path
import re

repo = Path(__file__).resolve().parents[1]
data = repo / 'formalization' / 'OddPiPowers' / 'OddPiPowers' / 'Arithmetic' / 'TwelveLayerCellData.lean'
source = data.read_text(encoding='utf-8')
cut_rows = []
for k in range(10):
    name = f'twelveCutWitnessRows{k}'
    match = re.search(rf'def {name} : List \(Nat × Nat\) := \[([\s\S]*?)\]', source)
    if not match:
        raise RuntimeError(f'missing {name}')
    cut_rows.extend((int(a), int(b)) for a, b in re.findall(r'\((\d+),\s*(\d+)\)', match.group(1)))
if len(cut_rows) != 1181:
    raise RuntimeError(f'expected 1181 cuts, got {len(cut_rows)}')
slopes = list(range(12)) + list(range(58, 70))
floor_codes = []
for (ln, ld), (rn, rd) in zip(cut_rows, cut_rows[1:]):
    mid = (Fraction(ln, ld) + Fraction(rn, rd)) / 2
    digits = [(s * mid).numerator // (s * mid).denominator for s in slopes]
    if any(d < 0 or d >= 70 for d in digits):
        raise RuntimeError(f'floor digit out of range: {digits}')
    floor_codes.append(sum(d * 70**i for i, d in enumerate(digits)))
if len(floor_codes) != 1180:
    raise RuntimeError(f'expected 1180 floor codes, got {len(floor_codes)}')
chunks = [floor_codes[i:i+100] for i in range(0, len(floor_codes), 100)]
lines = ['/- BEGIN generated floor codes -/']
for k, chunk in enumerate(chunks):
    vals = ', '.join(map(str, chunk))
    lines += [f'def twelveFloorCodeRows{k} : List Nat := [', f'  {vals}', ']']
lines += ['def twelveFloorCodeRows : List Nat :=']
lines += [f'  twelveFloorCodeRows{k}' + (' ++' if k+1 < len(chunks) else '') for k in range(len(chunks))]
lines += ['/- END generated floor codes -/']
block = '\n'.join(lines)
start = source.find('/- BEGIN generated floor codes -/')
if start >= 0:
    end = source.index('/- END generated floor codes -/', start) + len('/- END generated floor codes -/')
    source = source[:start] + block + source[end:]
else:
    source = source.replace('\nend OddPiPowers\n', '\n' + block + '\n\nend OddPiPowers\n')
data.write_text(source, encoding='utf-8')
print(f'cuts={len(cut_rows)}, cells={len(floor_codes)}, chunks={len(chunks)}, codeDigits={min(floor_codes)}..{max(floor_codes)}')
