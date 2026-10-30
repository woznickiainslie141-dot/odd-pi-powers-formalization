from pathlib import Path

repo = Path(__file__).resolve().parents[1]
lean_file = repo / 'formalization' / 'OddPiPowers' / 'OddPiPowers' / 'Arithmetic' / 'TwelveLayerCells.lean'
text = lean_file.read_text(encoding='utf-8')
marker = '/- BEGIN generated cell-validity chunks -/'
start = text.find(marker)
if start < 0:
    raise RuntimeError('missing insertion marker')
end_marker = '/- END generated cell-validity chunks -/'
end = text.find(end_marker, start)
if end < 0:
    raise RuntimeError('missing end marker')
chunks = []
for k in range(2, 30):
    offset = 40 * k
    count = min(40, 1180 - offset)
    chunk = f'(twelveLayerCellTable.drop {offset})' if count == 20 else f'((twelveLayerCellTable.drop {offset}).take {count})'
    chunks.append(f'''theorem twelveCellsChunk{k}_valid :
    {chunk}.all (fun c => c.Valid) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
  twelve_cell_data_norm_num
  native_decide
''')
proof = [
    'set_option maxRecDepth 100000 in',
    'theorem twelveLayerCellTable_all_valid :',
    '    ∀ c ∈ twelveLayerCellTable, c.Valid := by',
    '  intro c hc',
]
indent = 2
tail_name = 'hc'
for k in range(29):
    offset = 40 * k
    base = 'twelveLayerCellTable' if k == 0 else f'(twelveLayerCellTable.drop {offset})'
    chunk = f'(twelveLayerCellTable.take 40)' if k == 0 else f'((twelveLayerCellTable.drop {offset}).take 40)'
    next_tail = f'(twelveLayerCellTable.drop {offset + 40})'
    split_name = f'hsplit{k}'
    hchunk_name = f'hchunk{k}'
    htail_name = f'htail{k}'
    if k == 0:
        proof += [
            ' ' * indent + f'have {split_name} : c ∈ {chunk} ∨ c ∈ {next_tail} := by',
            ' ' * (indent + 2) + f'have htmp := {tail_name}',
            ' ' * (indent + 2) + f'rw [← List.take_append_drop 40 {base}] at htmp',
            ' ' * (indent + 2) + 'exact List.mem_append.mp htmp',
        ]
    proof += [
        ' ' * indent + f'rcases {split_name} with {hchunk_name} | {htail_name}',
        ' ' * indent + f'· simpa using (List.all_eq_true.mp twelveCellsChunk{k}_valid) c {hchunk_name}',
    ]
    if k < 28:
        proof += [
            ' ' * indent + f'· have hsplit{k+1} : c ∈ ((twelveLayerCellTable.drop {offset + 40}).take 40) ∨ c ∈ (twelveLayerCellTable.drop {offset + 80}) := by',
            ' ' * (indent + 4) + f'have htmp := {htail_name}',
            ' ' * (indent + 4) + f'rw [← List.take_append_drop 40 (twelveLayerCellTable.drop {offset + 40})] at htmp',
            ' ' * (indent + 4) + 'exact List.mem_append.mp htmp',
        ]
    else:
        proof += [
            ' ' * indent + f'· simpa using (List.all_eq_true.mp twelveCellsChunk29_valid) c {htail_name}',
        ]
    indent += 2
    tail_name = htail_name
chunks.append('\n'.join(proof))
new = marker + '\n' + '\n'.join(chunks) + '\n' + end_marker
text = text[:start] + new + text[end + len(end_marker):]
lean_file.write_text(text, encoding='utf-8')
print('generated chunk theorems 2-5')
