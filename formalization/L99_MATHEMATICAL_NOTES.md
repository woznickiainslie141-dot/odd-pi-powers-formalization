# L=99 parameter optimization

**Accepted on31 October2026.** Guarded compilation, four final signatures
and15 transitive axiom reports passed. See L99_CURRENT_CHECKPOINT.md and
OddPiPowers/logs/l99-acceptance-2026-10-31.json for executed evidence. Earlier
candidate wording describes the certificate-generation stage; its final
fixed conclusions are now accepted.

## Construction and analytic constants

Retain the accepted nested auxiliary-polynomial construction and irrationality
transfer theorem. Use L=99, offsets0,...,27, with64 copies at offset0 and4
copies at each other offset. Thus M=172 and m=171. Equivalently, scale the
base weights(16,1,...,1), of total43, by4. The actual interval family and its
grouping are defined in the independent namespace OddPiPowers.L99.

The sum of normalized interval lengths is4*(389/11). At the fixed rational
height Y=1801/20, exact finite log-series lower bounds and the cubic arctan
inequality give the conservative constants

    D0 >= 9789173/20000 = 489.45865,
    G0 <= 13452441/50000 = 269.04882.

The log normalization uses4096=2^12, so the log-series arguments are at
least1 at this height. The28 interval certificates are ordinary rational
proofs; Arb intervals do not occur as assumptions in Lean.

## Finite common-divisor certificate

The new exact endpoint partition has3004 cells, with56 labeled endpoints
and28 layer weights. Of these,3000 cells have a positive certified value.
Each cell records its rational endpoints, endpoint rank and inverse-rank
codes, floor code and minimum value. The kernel checks floor bounds,
adjacent endpoint ordering, permutation consistency and both gap and
endpoint costs. The general real-variable soundness proof then covers
every point in each open cell, including endpoint positions of the
inner minimization variable. No sample-grid argument is used.

For the prime-window rate, keep periods0,...,31 explicitly and estimate
the finite tail32,...,999999 by the existing rational telescoper. The
candidate floor sums are

    prefix >= 1380525198339888/10^14,
    tail   >=     381339545481/10^14.

The instantiated cell templates use relative shrink epsilon=10^(-56).
The symbolic loss bound is

    2*99^2*epsilon*1000000*43*3004/99.

The resulting base rate exceeds13.809065. Scaling the actual grouping
by4 gives the divisor rate gamma>=2761813/50000=55.23626, with arbitrary
positive asymptotic slack supplied by the proved finite-window PNT theorem.
Neither one million periods nor their enormous window product is enumerated
by the compiler; only the short prefix and rational tail inequalities are
checked computationally.

## Existing transfer and the exact target

After dividing by the actual common coefficient divisor, use

    D = 54469491/100000 = 544.69491,
    G = 2672657/12500   = 213.81256,
    D-2G = 117.06979 >0.

The accepted transfer theorem, with m=171 and k=3, gives the exact candidate

    171*(D+G)/(D-2G) = 12970477737/11706979
                     = 1107.9269670681... <1107.93.

The new final source is OddPiPowers/L99/Transfer/PiCube.lean. It targets the
unconditional ExponentUpperBound statement, a strict-bound witness, and the
standard not-LiouvilleWith corollary. The cofactor-transfer proposal is not
used. The slight difference from the Arb optimum near1107.9267863 comes
from the conservative rational rate bounds and the finite divisor estimate.

## Execution organization

The complete new dependency closure has147 modules. Independent20-cell
proof batches are co-located five at a time, giving31 validity bundles,
31 prefix bundles and31 tail bundles. Their individual proof bodies are
unchanged by bundling. The preliminary CellProbe source is separate from
the final closure. Finite decisions use `decide +kernel`, without native
evaluation or new mathematical axioms.

The unchanged bounded compiler runner serializes every trial under the
6144 MiB aggregate job cap,2048 MiB Lean cap and300-second limit. Initial
individual Lake checks and subsequent emitted Lean modules are recorded
with source hashes and guarded job metrics. The final signature and transitive axiom audit passed. Only propext,
Classical.choice and Quot.sound occur in the15 selected closures, including
the actual family and unconditional final theorem. All264 prior accepted P6
mathematical sources and pinned dependencies were verified unchanged. The
peak build job was4775.96 MiB and the audit4757.47 MiB. Whole-table reductions
that exceeded limits were replaced by structural append proofs and small
chunk statistics, preserving the already successful cost/numerical proofs.
