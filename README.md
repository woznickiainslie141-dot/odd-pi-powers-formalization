# Odd powers of pi: research notes and Lean formalization

Private working archive, prepared on **30 October 2026**. It contains the
current mathematical notes, manuscripts and PDFs, computational experiments,
Lean sources, proof-development records and executed acceptance evidence.

## Formally verified result

The accepted P1–P6 development proves the unconditional statement

$$
 \mu(\pi^3)\le \frac{42170551935}{35026168}
 =1203.9727535995\ldots<1203.973.
$$

The precise formal interface is `ExponentUpperBound`; it gives the rational
approximation lower bound for every positive exponent slack and all
sufficiently large positive denominators. The final theorem is:

```lean
OddPiPowers.pi_cube_exponentUpperBound_42170551935_div_35026168 :
  ExponentUpperBound (Real.pi ^ 3) (42170551935 / 35026168)
```

- [Final theorem source](formalization/OddPiPowers/OddPiPowers/Transfer/TwelveLayerPiCube.lean)
- [Current accepted checkpoint](formalization/P6_CURRENT_CHECKPOINT.md)
- [Mathematical account and validation scope](formalization/P6_REVIEW_2026-10-30.md)
- [Executed acceptance report](formalization/OddPiPowers/logs/p6-acceptance-2026-10-30.json)

The fixed theorem has no auxiliary-family, analytic, prime-rate or numerical
hypothesis. Its proof uses the actual twelve-layer Gaussian coefficient
family, the proved common divisor, analytic rates and kernel-checked rational
numerical inequalities. The imported prime-distribution results are proved
dependencies. The build and exact transitive axiom audits were executed
before this archive was prepared: 264 project library modules, 424 new
declarations audited in the final stage, and 602 prior declarations in the
regression audit. The audited axioms are only `propext`, `Classical.choice`
and `Quot.sound`; no `sorryAx`, project mathematical axiom or native-evaluation
axiom occurs in the accepted result's audited closure.

This statement concerns the accepted dependency closure. Scratch files,
historical experiments and unfinished proposals elsewhere in the archive
are not thereby certified. The archived evidence records an executed local
validation; this upload itself does not constitute a new build or an
independent mathematical review. No claim of a best bound in the literature
is made.

## Improvements and higher odd powers

The [review of the improvement plan](output/pdf/odd_pi_powers_notes/improvement_plan/review_against_accepted_P6_2026-10-30.md)
separates three further targets from the accepted theorem:

| Target | Status at this snapshot |
|---|---|
| 1191.027 using the same P6 family | A cofactor elimination argument is written; its new transfer theorem is not yet Lean-formalized |
| 1107.93 using the L=99 shape | An archived Arb certificate supports the manuscript application; a new Lean finite arithmetic certificate and specialization are needed |
| 1094.97 combining both changes | Depends on both extensions above; not an accepted Lean theorem |

General transfer machinery and actual-family analysis are reusable for other
odd powers. The numerical higher-power applications in the notes have not
all been instantiated and accepted in Lean. In particular, this repository
does not claim that every assertion in a manuscript or every experimental
number is formally verified.

## Contents

| Location | Contents |
|---|---|
| `formalization/OddPiPowers/` | Lean project, pinned dependency manifest, documentation, audit sources and execution logs |
| `formalization/P*_REVIEW_*.md` | Stage reviews and their historical acceptance scope |
| `output/pdf/odd_pi_powers_notes/` | English notes, TeX sources, computational certificates and improvement plan |
| `output/pdf/odd_pi_powers_notes.pdf` | Compiled notes; consult the current checkpoint for formalization status |
| `output/pdf/pi3_explicit_bound/` | Earlier manuscript and supporting files |
| `research/` | Research computations and notes |
| `scripts/` | Bounded compiler runners, audit utilities and numerical review tools |
| `logs/`, project `logs/` | Execution records, including failed or historical trials |
| `tmp/` | Retained exploratory material, literature and upstream PNT audit sources |

Older documents are retained as historical records and may describe earlier
unfinished states. The current P6 checkpoint and dated acceptance report
govern the present claim. Stronger numerical statements in a draft should
be read with their local proof and certification status.

## Toolchain and reproduction

The Lean project is pinned to **Lean v4.35.0** and Mathlib v4.35.0; the exact
transitive revisions are in
[`lake-manifest.json`](formalization/OddPiPowers/lake-manifest.json).
The required upstream PNT/Stirling proof subset and provenance are included
in the project sources. Preserve the manifest and toolchain rather than
updating dependencies to current versions.

Existing build products, downloaded dependencies and toolchain binaries are
excluded from this source snapshot. A fresh checkout needs the pinned Lean
installation and restoration of the exact manifest dependencies and suitable
caches. Such setup is separate from the archived validation evidence.

On Windows, all project proof trials use the bounded runner from the
repository root, for example:

```powershell
python scripts/bounded_lean.py OddPiPowers/Transfer/TwelveLayerPiCube.lean --timeout 300 --log logs/recheck-final.log
```

This single-file command requires its dependencies to have been compiled.
For serialized library validation inspect `scripts/guarded_library_build.py`
and the accepted build records. Do not start with a broad rebuild as a
recovery check. The resource contract is in [AGENTS.md](AGENTS.md): one
process tree, one worker, a 6144 MiB aggregate job cap, a 2048 MiB Lean cap,
at most 300 seconds per trial, and startup thresholds of 2560 MiB free
physical RAM and 12288 MiB free system commit. Do not overlap compiler
trials and generators or bypass these limits.

## Snapshot boundaries

This is a working-tree snapshot, rather than a migration of the old nested
Git histories. It retains project-authored working material, drafts, logs,
manuscripts, data and literature files. Exclusions are recorded in the
snapshot manifest: nested `.git` metadata, `.lake` and Python caches,
downloaded Mathlib cache archives, compiled Lean artifacts and the temporary
Lean toolchain installer archive. Those excluded local files are preserved
on disk. `SNAPSHOT_MANIFEST.json` lists included paths, byte sizes and SHA-256
hashes for checking the uploaded snapshot.

Third-party source and literature retain their original notices and
attribution. No new blanket license is granted by this archive.
