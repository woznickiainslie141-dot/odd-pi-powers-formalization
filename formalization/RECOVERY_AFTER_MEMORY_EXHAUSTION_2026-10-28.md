# Memory exhaustion and restart checkpoint — 28 October 2026

This inspection is diagnostic. It did not restart Lean compilation or change
mathematical source. All times below are UTC+8.

## Confirmed system evidence

Windows System event 2004, provider
`Microsoft-Windows-Resource-Exhaustion-Detector`, at **01:12:27** explicitly
reports virtual-memory exhaustion. Its structured event data record:

| Item | Bytes / value |
|---|---:|
| System commit charge | 46,820,659,200 |
| System commit limit | 46,934,056,960 |
| Commit limit used | 99.7584% |
| Physical RAM | 16,869,285,888 |
| Physical RAM in use | 15,865,835,520 |
| lean.exe PID 33588 commit | 7,310,127,104 (6.81 GiB) |
| lean.exe PID 48760 commit | 3,206,668,288 (2.99 GiB) |
| python.exe PID 22744 commit | 2,040,963,072 (1.90 GiB) |

The event records both Lean processes simultaneously: PID 48760 started at
01:07:23; PID 33588 started at 01:12:03. This is evidence of overlapping
compilation workloads. It does not attribute all system commit to this task
or establish the purpose of the Python process.

The OS boot time is **01:15:45**. Kernel-Power event 41 at 01:15:48 and
EventLog event 6008 report a non-clean restart. Virtual-memory exhaustion is
confirmed; the event sequence is consistent with the reported system hang
and forced restart, but does not by itself prove the exclusive cause of the
restart. The 6008 embedded previous-shutdown timestamp differs from the
resource-event time, so it is not used as an exact failure timestamp here.

An Application Error event at 01:05:51 separately records a pwsh/coreclr
exception 0xc00000fd. Do not conflate that earlier application fault with the
later confirmed virtual-memory exhaustion.

## State after restart

At approximately 01:24:

- No `lean.exe` or `lake.exe` process was running.
- Installed visible RAM: 15.71 GiB; free physical RAM at the diagnostic sample:
  3.97 GiB. Free commit capacity: 25.29 GiB of a 39.71 GiB post-reboot limit.
- The project directory, root source and manifest exist and are readable.
  `lean-toolchain` still pins v4.35.0.
- The task `P3-B：完成连续单元证书` has `systemError` status. Its latest turn
  failed after restart with **`workspace routing discovery failed`**.
- The persisted goal now has status **blocked**, updated at **01:18:37**.
  Its token budget is null. This is not the older paused-state diagnosis.

The post-restart routing error is distinct from Lean proof failure. Workspace
files are accessible from this chat; that does not establish that the other
task's application routing has recovered.

## Mathematical work to preserve

P1, P2 and P3-A have prior acceptance records. Their source files and logs
remain. No new complete build was performed during this diagnosis.

P3-B is incomplete. Preserve:

- `Arithmetic/ContinuousCarry.lean` and `CertifiedPrimeDivisor.lean`.
- `Arithmetic/TwelveLayerCellData.lean` and `TwelveLayerCellChunks.lean`.
- The current `TwelveLayerCells.lean` refactor toward adjacent-order checks
  and per-row kernel proofs, last modified at 01:10:56.
- `TwelveLayerCost.lean`, whose earlier rewrite errors were repaired in the
  preceding run, but whose current dependency chain is not accepted.
- All existing `logs/p3b-*.log` files.

Only the data and chunk modules have current .olean artifacts in the
twelve-layer group at inspection. The current `TwelveLayerCells.lean` has no
successful compiled artifact. The latest per-row build log ends before a
successful completion result. The historical 131-entry root audit does not
cover these new modules.

Some preceding handoff prose says there are still 30 `native_decide` proofs.
The current source has since been refactored; inspect the current active
declarations rather than replaying that historical count. Removing native
evaluation text is not proof of kernel acceptance: the replacement must
compile, and its transitive axiom set must be audited.

## Resource-aware recovery boundary

1. Restore the original task's workspace routing before resuming autonomous
   proof work. Do not interpret a delivered message as lifecycle recovery.
2. Use one Lean process, one small proof block and one worker initially.
   Confirm the preceding process has actually exited before starting another.
   Do not overlap generators or independent compiler probes.
3. Configure an explicit per-process memory limit for a small trial; the
   installed Lean help exposes `--memory` and `--threads`. A worker-count
   setting alone is not evidence that separate builds cannot overlap.
4. Measure that small trial before expanding proof batches. If it exceeds the
   limit, change the proof representation or split modules further instead of
   repeating unrestricted whole-table reduction.
5. Preserve the manifest, toolchain and cache. Do not clear `.lake`, reinstall
   Lean, restart a full-root build as a health check, or accept draft numerical
   proofs on the strength of old build logs.

The next mathematical target remains a kernel-checkable, resource-bounded
certificate proof, followed by the continuous lower function, actual divisor
application, root integration and executed axiom audit.
