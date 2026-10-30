# L=99 numerical instance: current checkpoint

Assigned on 31 October 2026: retain the existing transfer theorem, change
the shape to L=99, offsets 0,...,27 and counts (64,4,...,4), prove the
fixed pi-cube exponent below 1107.93, compile and audit the new closure,
then upload it to the existing private GitHub repository.

P1–P6 remain accepted and their mathematical sources must stay unchanged.
The new application is not accepted yet. Work belongs in independent L99
modules; no cofactor-transfer improvement or higher-power application is
part of this assignment.

The fixed rational height 1801/20 has been freshly checked with the original
256-bit Arb certifier: E=1107.92678654807...<1107.93. This numerical replay
does not constitute a Lean proof. Evidence is in
output/pdf/odd_pi_powers_notes/improvement_plan/experiments/p6_review_2026-10-30/L99.json.

Next: new exact carry cells and ordinary kernel validity, finite prime-window
rate, actual grouping, analytic rational certificates, transfer, guarded
build and exact transitive axiom audit. Preserve every accepted source,
toolchain, manifest and cache. All compilation uses scripts/bounded_lean.py
under the existing resource contract; do not overlap generation/compilation.

## Live execution and recovery

The serial orchestrator is scripts/build_l99.py --emit. Its authoritative
ledger is formalization/OddPiPowers/logs/l99-build-state.json. It reuses a
record only after checking all transitive project source hashes, pinned
configuration and successful guarded job evidence. It never runs parallel
proofs. Check for a live process before restarting it; do not overlap a new
runner with the current one.

147 new closure modules are generated in OddPiPowers/L99; the additional
CellProbe module is only a preliminary feasibility check. The ordinary
kernel mode `decide +kernel` is used for ground finite certificates, without
native evaluation. All3004 literal cells, general soundness/cost, actual
shape/grouping, whole-table validity, lengths/counts and chain/disjointness
proofs have passed. All28 exact analytic certificates and the numerical rate
assembly have passed. Cell/period windows, scaling, shrunken templates and
symbolic prefix/tail interfaces have also passed. The ordered run now checks
the31 finite prefix bundles, followed by31 tail bundles.
To reduce import overhead, five independent20-cell proof batches are
co-located in each validity/prefix/tail bundle (31 bundles of each kind).
The proof bodies are unchanged. The ledger is authoritative for progress.

The initial whole-table length/count/chain reductions exceeded the unchanged
Lean limits. They were replaced by chunk statistics and structural append
proofs in TwentyEightLayerCellStats/Cells/CellOrder. Local irreducibility
attributes only control elaboration; no unsafe reducibility option is used.
All successful3004 cost proofs were preserved and reused. No resource cap,
runner, accepted source or pinned dependency was changed. One transient Git
metadata startup failure succeeded on a single guarded retry.

Reproducible generation, with no compiler active: run
scripts/generate_l99_instance.py --cells, then --rates, then --bundle.
Generation replaces only the new, unaccepted L99 candidate sources.

Candidate constants are gamma=2761813/50000, D=54469491/100000,
G=2672657/12500, giving E=12970477737/11706979=1107.9269670681... .
The finite base-rate candidate is about13.8090653788, exceeding the
required13.809065. None of those new fixed claims is accepted yet.

The final target is OddPiPowers.L99.Transfer.PiCube. After its compilation,
run scripts/verify_l99_acceptance.py --prepare with no compiler active;
compile L99AcceptanceAudit.lean using bounded_lean.py and log exactly
logs/l99-acceptance-axioms.log; then run scripts/verify_l99_acceptance.py.
The verifier checks new compilation evidence, all264 unchanged P6 sources,
the manifest/toolchain and15 exact axiom reports plus four final signatures.
Only then update claim/status documentation and the private GitHub snapshot.
