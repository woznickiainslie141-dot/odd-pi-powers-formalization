"""Split the existing exact candidate arrays into 40-cell Lean chunks."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "OddPiPowers" / "Arithmetic" / "TwelveLayerCellData.lean"
OUTPUT = ROOT / "OddPiPowers" / "Arithmetic" / "TwelveLayerCellChunks.lean"
source = SOURCE.read_text(encoding="utf-8")


def definition_body(name: str) -> str:
    match = re.search(
        rf"def\s+{re.escape(name)}\s*:\s*List.*?:=\s*\[(.*?)\n\]",
        source,
        flags=re.S,
    )
    if not match:
        raise ValueError(f"could not find list definition {name}")
    return match.group(1)


def pair_chunks(prefix: str, count: int) -> list[tuple[int, int]]:
    result = []
    for index in range(count):
        body = definition_body(f"{prefix}{index}")
        result.extend((int(a), int(b)) for a, b in re.findall(r"\((\d+)\s*,\s*(\d+)\)", body))
    return result


def nat_chunks(prefix: str, count: int) -> list[int]:
    result = []
    for index in range(count):
        body = definition_body(f"{prefix}{index}")
        result.extend(int(value) for value in re.findall(r"\d+", body))
    return result


cuts = pair_chunks("twelveCutWitnessRows", 10)
rank_values = pair_chunks("twelveRankValueRows", 10)
order_codes = nat_chunks("twelveOrderCodeRows", 12)
floor_codes = nat_chunks("twelveFloorCodeRows", 12)

if (len(cuts), len(rank_values), len(order_codes), len(floor_codes)) != (1181, 1180, 1180, 1180):
    raise ValueError(
        "unexpected source lengths: "
        f"cuts={len(cuts)}, rank/value={len(rank_values)}, "
        f"order={len(order_codes)}, floor={len(floor_codes)}"
    )
if any(den == 0 for _, den in cuts):
    raise ValueError("candidate cut has zero denominator")

rows = []
for index, ((rank_code, value), order_code, floor_code) in enumerate(
    zip(rank_values, order_codes, floor_codes)
):
    left_num, left_den = cuts[index]
    right_num, right_den = cuts[index + 1]
    rows.append(
        "  { leftNumerator := %d, leftDenominator := %d, "
        "rightNumerator := %d, rightDenominator := %d, "
        "rankCode := %d, orderCode := %d, floorCode := %d, value := %d }"
        % (left_num, left_den, right_num, right_den, rank_code, order_code, floor_code, value)
    )

lines = [
    "module",
    "",
    "import Init.Prelude",
    "",
    "@[expose] public section",
    "",
    "namespace OddPiPowers",
    "",
    "/-- Raw exact data for one twelve-layer rational cell. -/",
    "structure TwelveCellRawData where",
    "  leftNumerator : Nat",
    "  leftDenominator : Nat",
    "  rightNumerator : Nat",
    "  rightDenominator : Nat",
    "  rankCode : Nat",
    "  orderCode : Nat",
    "  floorCode : Nat",
    "  value : Nat",
    "  deriving DecidableEq, Repr",
    "",
]

chunk_names = []
for chunk_index in range(30):
    start = chunk_index * 40
    chunk = rows[start : start + 40]
    name = f"twelveCellRawDataRows{chunk_index}"
    chunk_names.append(name)
    lines.append(f"def {name} : List TwelveCellRawData := [")
    lines.append(",\n".join(chunk))
    lines.extend(["]", ""])

lines.append("def twelveCellRawDataRows : List TwelveCellRawData :=")
lines.append("  " + " ++\n  ".join(chunk_names))
lines.extend(["", "end OddPiPowers", ""])
OUTPUT.write_text("\n".join(lines), encoding="utf-8")
print(f"wrote {len(rows)} rows in 30 chunks to {OUTPUT}")
