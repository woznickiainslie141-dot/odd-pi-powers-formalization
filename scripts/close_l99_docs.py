"""Publish local status documentation only after executed L99 acceptance."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
report=json.loads((ROOT/'formalization/OddPiPowers/logs/l99-acceptance-2026-10-31.json').read_text(encoding='utf-8'))
assert report['status']=='accepted' and report['new_closure_modules']==147

readme=r'''# Odd powers of pi: research notes and Lean formalization

Private research archive, updated on **31 October 2026**. It contains Lean
sources, manuscripts and PDFs, experiments, data, and executed verification
records. Historical drafts retain their own proof and certification status.

## Latest accepted result: L=99

$$
\mu(\pi^3)\le\frac{12970477737}{11706979}
=1107.9269670681\ldots<1107.93.
$$

The unconditional Lean statement is:

```lean
OddPiPowers.L99.pi_cube_exponentUpperBound_l99_exact :
  ExponentUpperBound (Real.pi ^ 3) (12970477737 / 11706979)
```

`ExponentUpperBound` quantifies over all integer numerators and sufficiently
large positive denominators, with every positive exponent slack. A strict
upper-bound witness and a standard not-LiouvilleWith corollary are included.

- [Final theorem source](formalization/OddPiPowers/OddPiPowers/L99/Transfer/PiCube.lean)
- [Accepted checkpoint](formalization/L99_CURRENT_CHECKPOINT.md)
- [Mathematical notes and exact constants](formalization/L99_MATHEMATICAL_NOTES.md)
- [Executed acceptance report](formalization/OddPiPowers/logs/l99-acceptance-2026-10-31.json)
- [Final signature and axiom audit](formalization/OddPiPowers/logs/l99-acceptance-axioms.log)

This is a parameter optimization of the accepted nested construction and
existing transfer theorem. Use28 layers, offsets0,...,27, multiplicities
(64,4,...,4), degree171 and fixed height1801/20. The actual3004-cell
arithmetic certificate, finite-window divisor rate and one-sided rational
analytic estimates are proved. No cofactor-transfer improvement is used.

All147 new dependency modules were compiled through the bounded runner.
Four final signatures and15 exact transitive axiom reports passed. The
audited closures, including the actual auxiliary family and final theorem,
use only `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx`, new
mathematical axiom or native-evaluation axiom occurs in the accepted closure.
All264 earlier P6 mathematical source files and the pinned dependencies were
verified unchanged. Peak build job:4775.96 MiB; final audit:4757.47 MiB.

## Earlier accepted work and remaining proposals

P1–P6 remain accepted, including the earlier unconditional bound
42170551935/35026168=1203.9727535995..., strictly below1203.973.
Read the [P6 checkpoint](formalization/P6_CURRENT_CHECKPOINT.md),
[review](formalization/P6_REVIEW_2026-10-30.md) and
[executed acceptance report](formalization/OddPiPowers/logs/p6-acceptance-2026-10-30.json).
The earlier root and mathematical sources are retained unchanged.

| Target or application | Status at this snapshot |
|---|---|
| L99 exponent below1107.93 | **Accepted in Lean**, exact exponent12970477737/11706979 |
| Cofactor transfer, potentially below1094.97 with L99 | Mathematical proposal; new transfer theorem not yet formalized |
| Higher odd-power numerical applications | General machinery exists, but the manuscript's numerical cases are not all Lean-accepted |
| L=129 or L=175 search candidates | Experimental values; not accepted fixed Lean applications |

See the [improvement-plan review](output/pdf/odd_pi_powers_notes/improvement_plan/review_against_accepted_P6_2026-10-30.md)
for the pre-L99 analysis. Its dated statements that L99 still needs
formalization are historical. This archive does not certify every assertion
in a draft, every experiment, or every scratch file. The executed records
describe local formal verification; no claim of independent mathematical
review or a best bound in the current literature is made.

## Contents

| Path | Contents |
|---|---|
| `formalization/OddPiPowers/` | Lean project, exact dependency manifest, provenance, documentation and verification logs |
| `formalization/L99_*.md` | Current accepted application, mathematical explanation and development history |
| `formalization/P*_REVIEW_*.md` | Earlier stage reviews and their accepted scope |
| `output/pdf/odd_pi_powers_notes/` | English TeX notes, computational certificates and improvement plan |
| `output/pdf/odd_pi_powers_notes.pdf` | Earlier compiled notes; current formalization status is given above |
| `output/pdf/pi3_explicit_bound/` | Earlier manuscript and supporting material |
| `research/` | Research computations and notes |
| `scripts/` | Bounded compiler runners, generators, verifiers and snapshot utilities |
| `logs/` and project `logs/` | Execution evidence, including historical and failed trials |
| `tmp/` | Retained exploratory material, literature and upstream PNT audit sources |

## Toolchain and reproduction

The project pins Lean and Mathlib **v4.35.0**. Preserve `lean-toolchain` and
[`lake-manifest.json`](formalization/OddPiPowers/lake-manifest.json); the
needed proved PNT/Stirling subset is vendored with provenance. Build products,
dependency checkouts and toolchain binaries are excluded from this archive.
A fresh checkout must first restore the exact dependencies and compile or
restore the accepted base modules. The original base validation utility is
`scripts/guarded_library_build.py`.

From the workspace root on Windows, after restoring those prerequisites:

```powershell
python scripts/build_l99.py --emit
python scripts/verify_l99_acceptance.py --prepare
python scripts/bounded_lean.py L99AcceptanceAudit.lean --timeout 300 --log logs/l99-acceptance-axioms.log
python scripts/verify_l99_acceptance.py
```

The first command compiles the new closure serially. Cached records are
reused only when the transitive project sources, pinned configuration and
successful guarded evidence match and the artifacts exist. Its final entry
is `OddPiPowers.L99.Transfer.PiCube`. Audit preparation and generators must
not overlap a compiler process. Existing logs and acceptance records are
preserved as evidence rather than treated as a replacement for missing
compiled artifacts.

Follow [AGENTS.md](AGENTS.md): one process tree and worker,6144 MiB aggregate
job cap,2048 MiB Lean cap, at most300 seconds per trial, and startup gates
of2560 MiB free physical RAM and12288 MiB free system commit. Never bypass
the runner, run parallel proofs, raise limits, clear needed caches or change
paging settings. Failed large reductions are split into small proved blocks.

## Snapshot boundaries and third-party material

This is a working-tree archive, not a migration of the old nested Git
histories. It retains project sources, drafts, logs, manuscripts, data and
literature. `SNAPSHOT_MANIFEST.json` records included paths, sizes and SHA-256
hashes and identifies exclusions: nested Git metadata, `.lake` and Python
caches, compiled Lean artifacts, downloaded Mathlib cache archives and the
temporary Lean installer archive. Excluded local files remain on disk.
Third-party sources and literature retain their original notices; no new
blanket license is granted by this private archive.
'''
(ROOT/'README.md').write_text(readme,encoding='utf-8')

checkpoint='''# L99 accepted checkpoint

**Complete and accepted on31 October2026.** The user-assigned L=99 parameter
optimization is proved, with exact exponent12970477737/11706979,
approximately1107.9269670681 and strictly below1107.93.

    OddPiPowers.L99.pi_cube_exponentUpperBound_l99_exact :
      ExponentUpperBound (Real.pi ^ 3) (12970477737 / 11706979)

Final source: OddPiPowers/OddPiPowers/L99/Transfer/PiCube.lean, relative to
this formalization directory. Read L99_MATHEMATICAL_NOTES.md and the executed
report OddPiPowers/logs/l99-acceptance-2026-10-31.json. The old live notes are
archived in L99_PROGRESS_HISTORY_2026-10-31.md.

## Executed evidence

- All147 new dependency modules compiled successfully, using the unchanged
  bounded_lean.py guard. The ledger is OddPiPowers/logs/l99-build-state.json.
- Four final signatures and15 exact transitive axiom reports passed in
  OddPiPowers/logs/l99-acceptance-axioms.log. Only propext, Classical.choice
  and Quot.sound occur, including in the actual family and final theorem.
- Peak new build job4775.96 MiB; final audit4757.47 MiB, below6144 MiB.
- All264 prior P6 mathematical sources, the manifest, Lean v4.35.0 and all
  pinned dependency revisions were verified unchanged.
- Whole-table reductions that exceeded the existing limits were replaced
  by chunk statistics and structural append proofs. All3004 cost proofs
  and62 numerical prefix/tail bundles were preserved. Two transient Git
  metadata startup failures recovered with guarded retries; dependency
  objects and revisions were checked, without deleting caches or changing
  resource limits.
- scripts/verify_l99_acceptance.py returned status=accepted. No mathematical,
  compiler or audit obligation remains for this fixed L99 application.

## Exact instance and future scope

L=99, offsets0,...,27, counts(64,4,...,4), M=172, m=171, Y=1801/20.
gamma=2761813/50000, D=54469491/100000, G=2672657/12500.
The existing transfer is used; cofactor improvements and other odd-power
numerical applications are not part of this acceptance.

Preserve all accepted L99 and P1–P6 sources, toolchain, manifest and caches.
Do not resume archived running/draft instructions or regenerate accepted
tables without a new assignment. Compiler access remains serial and guarded
by the existing memory/time contract.

The authorized repository is the existing private
woznickiainslie141-dot/odd-pi-powers-formalization. The final GitHub commit and
the local upload verification receipt record synchronization of this result.
'''
(ROOT/'formalization/L99_CURRENT_CHECKPOINT.md').write_text(checkpoint,encoding='utf-8')

notes=ROOT/'formalization/L99_MATHEMATICAL_NOTES.md'
text=notes.read_text(encoding='utf-8')
start=text.index('Date:');end=text.index('## Construction')
text=text[:start]+'''**Accepted on31 October2026.** Guarded compilation, four final signatures
and15 transitive axiom reports passed. See L99_CURRENT_CHECKPOINT.md and
OddPiPowers/logs/l99-acceptance-2026-10-31.json for executed evidence. Earlier
candidate wording describes the certificate-generation stage; its final
fixed conclusions are now accepted.

'''+text[end:]
text=text.replace('The complete new dependency closure has146 modules.','The complete new dependency closure has147 modules.')
start=text.index('The final import/signature')
text=text[:start]+'''The final signature and transitive axiom audit passed. Only propext,
Classical.choice and Quot.sound occur in the15 selected closures, including
the actual family and unconditional final theorem. All264 prior accepted P6
mathematical sources and pinned dependencies were verified unchanged. The
peak build job was4775.96 MiB and the audit4757.47 MiB. Whole-table reductions
that exceeded limits were replaced by structural append proofs and small
chunk statistics, preserving the already successful cost/numerical proofs.
'''
notes.write_text(text,encoding='utf-8')

project_readme=ROOT/'formalization/OddPiPowers/README.md'
text=project_readme.read_text(encoding='utf-8')
title='# Odd powers of pi: accepted Lean formalization\n\n'
text=text.replace(title,title+'''**The L99 application is accepted on31 October2026.** The latest theorem
`OddPiPowers.L99.pi_cube_exponentUpperBound_l99_exact` proves
`ExponentUpperBound (Real.pi ^ 3) (12970477737 / 11706979)`, strictly
below1107.93. All147 new closure modules, four final signatures and15 axiom
reports passed. Read the [L99 checkpoint](../L99_CURRENT_CHECKPOINT.md),
[notes](../L99_MATHEMATICAL_NOTES.md) and
[executed report](logs/l99-acceptance-2026-10-31.json).
From the workspace root, `python scripts/build_l99.py --emit` serializes
this closure after its accepted base dependencies are restored. All264
earlier P6 mathematical sources and pinned dependencies are unchanged.

The P1–P6 record below describes the retained earlier instance.

''',1)
text=text.replace('cofactor-transfer improvement, new numerical shapes','cofactor-transfer improvement, other new numerical shapes')
project_readme.write_text(text,encoding='utf-8')

agents=ROOT/'AGENTS.md';text=agents.read_text(encoding='utf-8')
start=text.index('On 31 October');end=text.index('Read formalization/P3B_MEMORY_BOUNDED_GOAL.md',start)
text=text[:start]+'''The L99 parameter optimization is complete and accepted on31 October2026:
ExponentUpperBound(pi^3,12970477737/11706979), strictly below1107.93.
Read formalization/L99_CURRENT_CHECKPOINT.md and its executed acceptance
report before continuing. All147 new modules, final signatures and fresh
axiom audit passed. Preserve the accepted L99 and P1–P6 sources. No L99
proof obligation remains; cofactor and higher-power applications need a new
assignment. The authorized backup is the existing private GitHub repository
woznickiainslie141-dot/odd-pi-powers-formalization.

'''+text[end:]
agents.write_text(text,encoding='utf-8')

plan=ROOT/'output/pdf/odd_pi_powers_notes/improvement_plan/assessment_and_optimization_plan.md'
text=plan.read_text(encoding='utf-8');heading=text.index('\n')+1
text=text[:heading]+'''
> **2026-10-31：L=99 已通过 Lean 验收。** 沿用原传递定理，精确上界为
> `12970477737/11706979 = 1107.9269670681… < 1107.93`。
> 新依赖闭包147个模块及最终签名/公理审计均通过；原P6全部264个数学源文件保持不变。
> 见项目根目录 `formalization/L99_CURRENT_CHECKPOINT.md` 与
> `formalization/OddPiPowers/logs/l99-acceptance-2026-10-31.json`。
> 以下较早状态记录保留为历史；余子式传递改进尚未形式化。
'''+text[heading:]
plan.write_text(text,encoding='utf-8')
print('Updated accepted L99 status, mathematical notes, README files and resource instructions.')
