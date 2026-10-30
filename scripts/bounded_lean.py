"""Run one Lean file in a memory-limited Windows job; never launches a build graph."""
import argparse
import ctypes as C
from ctypes import wintypes as W
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import re
import tomllib

if os.name != "nt":
    raise SystemExit("This guard requires Windows job objects.")
k = C.WinDLL("kernel32", use_last_error=True)
SIZE = C.c_size_t

class BasicLimits(C.Structure):
    _fields_ = [("process_time", C.c_longlong), ("job_time", C.c_longlong),
                ("flags", W.DWORD), ("min_ws", SIZE), ("max_ws", SIZE),
                ("active", W.DWORD), ("affinity", SIZE),
                ("priority", W.DWORD), ("scheduling", W.DWORD)]

class IO(C.Structure):
    _fields_ = [(n, C.c_ulonglong) for n in ("ro", "wo", "oo", "rb", "wb", "ob")]

class Limits(C.Structure):
    _fields_ = [("basic", BasicLimits), ("io", IO), ("process_memory", SIZE),
                ("job_memory", SIZE), ("peak_process", SIZE), ("peak_job", SIZE)]

class Startup(C.Structure):
    _fields_ = [("cb", W.DWORD), ("reserved", W.LPWSTR), ("desktop", W.LPWSTR),
                ("title", W.LPWSTR), ("x", W.DWORD), ("y", W.DWORD),
                ("xs", W.DWORD), ("ys", W.DWORD), ("xc", W.DWORD),
                ("yc", W.DWORD), ("fill", W.DWORD), ("flags", W.DWORD),
                ("show", W.WORD), ("cb_reserved", W.WORD), ("reserved2", C.c_void_p),
                ("stdin", W.HANDLE), ("stdout", W.HANDLE), ("stderr", W.HANDLE)]

class ProcessInfo(C.Structure):
    _fields_ = [("process", W.HANDLE), ("thread", W.HANDLE),
                ("pid", W.DWORD), ("tid", W.DWORD)]

class Memory(C.Structure):
    _fields_ = [("length", W.DWORD), ("load", W.DWORD)] + [
        (n, C.c_ulonglong) for n in ("total_phys", "free_phys", "total_commit",
                                    "free_commit", "total_virtual", "free_virtual", "extended")]

class ProcessEntry(C.Structure):
    _fields_ = [("size", W.DWORD), ("usage", W.DWORD), ("pid", W.DWORD),
                ("heap", SIZE), ("module", W.DWORD), ("threads", W.DWORD),
                ("parent", W.DWORD), ("priority", W.LONG), ("flags", W.DWORD),
                ("exe", W.WCHAR * 260)]

def api(name, restype, *args):
    f = getattr(k, name)
    f.restype, f.argtypes = restype, list(args)
    return f

close = api("CloseHandle", W.BOOL, W.HANDLE)
mutex_create = api("CreateMutexW", W.HANDLE, C.c_void_p, W.BOOL, W.LPCWSTR)
mutex_release = api("ReleaseMutex", W.BOOL, W.HANDLE)
job_create = api("CreateJobObjectW", W.HANDLE, C.c_void_p, W.LPCWSTR)
job_limit = api("SetInformationJobObject", W.BOOL, W.HANDLE, C.c_int, C.c_void_p, W.DWORD)
job_query = api("QueryInformationJobObject", W.BOOL, W.HANDLE, C.c_int, C.c_void_p, W.DWORD, C.c_void_p)
job_assign = api("AssignProcessToJobObject", W.BOOL, W.HANDLE, W.HANDLE)
job_kill = api("TerminateJobObject", W.BOOL, W.HANDLE, W.UINT)
process_kill = api("TerminateProcess", W.BOOL, W.HANDLE, W.UINT)
resume = api("ResumeThread", W.DWORD, W.HANDLE)
wait = api("WaitForSingleObject", W.DWORD, W.HANDLE, W.DWORD)
exit_code = api("GetExitCodeProcess", W.BOOL, W.HANDLE, C.POINTER(W.DWORD))
memory_status = api("GlobalMemoryStatusEx", W.BOOL, C.POINTER(Memory))
snapshot = api("CreateToolhelp32Snapshot", W.HANDLE, W.DWORD, W.DWORD)
process_first = api("Process32FirstW", W.BOOL, W.HANDLE, C.POINTER(ProcessEntry))
process_next = api("Process32NextW", W.BOOL, W.HANDLE, C.POINTER(ProcessEntry))
create = api("CreateProcessW", W.BOOL, W.LPCWSTR, W.LPWSTR, C.c_void_p,
             C.c_void_p, W.BOOL, W.DWORD, C.c_void_p, W.LPCWSTR,
             C.POINTER(Startup), C.POINTER(ProcessInfo))

def checked(ok):
    if not ok:
        raise C.WinError(C.get_last_error())
    return ok

def available():
    m = Memory(); m.length = C.sizeof(m)
    checked(memory_status(C.byref(m)))
    return m

def other_compilers():
    handle = snapshot(2, 0)
    if handle == C.c_void_p(-1).value:
        raise C.WinError(C.get_last_error())
    found = []
    try:
        entry = ProcessEntry(); entry.size = C.sizeof(entry)
        ok = process_first(handle, C.byref(entry))
        while ok:
            if entry.exe.lower() in ("lean.exe", "lake.exe"):
                found.append(f"{entry.exe}:{entry.pid}")
            ok = process_next(handle, C.byref(entry))
    finally:
        close(handle)
    return found

def run_job(command, cwd, log, mib, seconds, check_memory=True, env_overrides=None):
    import msvcrt
    mutex = checked(mutex_create(None, True, "Local\\OddPiPowersBoundedLean"))
    if C.get_last_error() == 183:
        close(mutex)
        raise RuntimeError("Another guarded proof is running; no second process started.")
    job = None; pi = ProcessInfo(); started = False; done = False
    try:
        m = available()
        if check_memory and (m.free_phys < 2560 * 2**20 or m.free_commit < 12288 * 2**20):
            raise RuntimeError("Insufficient free RAM/commit for a trial; nothing started.")
        job = checked(job_create(None, None))
        limits = Limits(); limits.basic.flags = 0x2000 | 0x200 | 0x8
        # Direct toolchain Lake plus one child; no second Lean worker can start.
        limits.basic.active = 2
        limits.job_memory = mib * 2**20
        checked(job_limit(job, 9, C.byref(limits), C.sizeof(limits)))
        log.parent.mkdir(parents=True, exist_ok=True)
        with log.open("ab", buffering=0) as output, open(os.devnull, "rb") as null:
            si = Startup(); si.cb = C.sizeof(si); si.flags = 0x100
            for f in (output, null): os.set_inheritable(f.fileno(), True)
            si.stdout = si.stderr = msvcrt.get_osfhandle(output.fileno())
            si.stdin = msvcrt.get_osfhandle(null.fileno())
            env = dict(os.environ, LEAN_NUM_THREADS="1")
            env.update(env_overrides or {})
            envblock = C.create_unicode_buffer("\0".join(f"{a}={b}" for a,b in sorted(env.items())) + "\0\0")
            cmd = C.create_unicode_buffer(subprocess.list2cmdline(command))
            checked(create(None, cmd, None, None, True, 0x4 | 0x400 | 0x08000000,
                           C.cast(envblock, C.c_void_p), str(cwd), C.byref(si), C.byref(pi)))
            started = True
            # The process is suspended until it is inside the limited job.
            checked(job_assign(job, pi.process))
            if resume(pi.thread) == 0xFFFFFFFF:
                raise C.WinError(C.get_last_error())
            begin = time.monotonic()
            print(f"pid={pi.pid} job_cap_MiB={mib} timeout_s={seconds} log={log}", flush=True)
            while True:
                status = wait(pi.process, 1000)
                if status == 0:
                    code = W.DWORD(); checked(exit_code(pi.process, C.byref(code)))
                    done = True
                    return code.value
                if status != 258:
                    raise C.WinError(C.get_last_error())
                m = available()
                if time.monotonic() - begin > seconds:
                    raise RuntimeError("Trial time limit reached; this job was terminated.")
                if check_memory and (m.free_phys < 512 * 2**20 or m.free_commit < 2048 * 2**20):
                    raise RuntimeError("System memory low-water mark reached; this job was terminated.")
    finally:
        if started and not done:
            if job: job_kill(job, 124)
            process_kill(pi.process, 124)
        if pi.thread: close(pi.thread)
        if pi.process: close(pi.process)
        if job:
            measured = Limits()
            if job_query(job, 9, C.byref(measured), C.sizeof(measured), None):
                record = {"job_cap_MiB": mib, "peak_job_MiB": round(measured.peak_job / 2**20, 2),
                          "process_completed": done, "exit_code": int(code.value) if done else None}
                log.with_suffix(".job.json").write_text(json.dumps(record, indent=2), encoding="utf-8")
                print("job_metrics=" + json.dumps(record), flush=True)
            close(job)  # KILL_ON_JOB_CLOSE also removes any remaining children.
        mutex_release(mutex); close(mutex)

def main():
    p = argparse.ArgumentParser()
    p.add_argument("file", nargs="?")
    p.add_argument("--timeout", type=int, default=180)
    p.add_argument("--log", default="logs/bounded-lean.log")
    p.add_argument("--self-test", action="store_true")
    p.add_argument("--emit", action="store_true", help="Emit this file's compiled artifact inside .lake.")
    p.add_argument("--build-target", help="Run a project Lake target inside the same hard-limited job.")
    a = p.parse_args()
    workspace = Path(__file__).resolve().parent.parent
    project = workspace / "formalization" / "OddPiPowers"
    log = (project / a.log).resolve()
    if not log.is_relative_to(project / "logs") or log.suffix != ".log":
        p.error("Log must be a .log file inside the project's logs directory.")
    if not 1 <= a.timeout <= 300: p.error("Trial timeout must be 1..300 seconds.")
    if a.self_test:
        log = project / "logs" / "bounded-lean-self-test.log"
        code = run_job([sys.executable, "-c", "x=bytearray(96*1024*1024); print('CAP_FAILED')"],
                       project, log, 48, 20, False)
        data = log.read_text(errors="replace")
        if code == 0 or "MemoryError" not in data or "CAP_FAILED" in data:
            raise RuntimeError(f"Memory-cap self-test failed, exit={code}; inspect {log}")
        print("PASS: the Windows job rejected a 96 MiB allocation under a 48 MiB cap.")
        return 0
    if bool(a.file) == bool(a.build_target):
        p.error("Supply exactly one Lean source file or --build-target.")
    lake = shutil.which("lake.exe") or shutil.which("lake")
    if not lake: raise RuntimeError("Lake is not on PATH; do not reinstall the toolchain.")
    elan = shutil.which("elan.exe") or shutil.which("elan")
    if not elan: raise RuntimeError("Elan selector is unavailable; no unguarded fallback.")
    selected = subprocess.run([elan, "which", "lake"], cwd=project,
                              capture_output=True, text=True, check=True).stdout.strip()
    if not Path(selected).is_file(): raise RuntimeError("Pinned Lake executable is missing.")
    lake = selected
    git = shutil.which("git.exe") or shutil.which("git")
    if not git: raise RuntimeError("Git is unavailable.")
    git_exec = subprocess.run([git, "--exec-path"], cwd=project,
                              capture_output=True, text=True, check=True).stdout.strip()
    git_bin = Path(git_exec).parent.parent / "bin"
    if not (git_bin / "git.exe").is_file():
        raise RuntimeError("Direct Git binary not found; no process-limit bypass.")
    child_env = {"PATH": str(git_bin) + os.pathsep + os.environ.get("PATH", "")}
    existing = other_compilers()
    if existing:
        raise RuntimeError("Another Lean/Lake process already exists: " + ", ".join(existing))
    if a.build_target:
        if a.emit or not re.fullmatch(r"OddPiPowers(?:\.[A-Za-z_][A-Za-z_0-9]*)*", a.build_target):
            p.error("Build targets must belong to OddPiPowers; --emit is for source checks.")
        with (project / "lakefile.toml").open("rb") as f:
            config = tomllib.load(f)
        libs = config.get("lean_lib", [])
        if not any(lib.get("name") == "OddPiPowers" and
                   {"--threads=1", "--memory=2048"}.issubset(lib.get("moreLeanArgs", []))
                   for lib in libs):
            raise RuntimeError("Lake library does not preserve the required Lean limits.")
        command = [lake, "--fail-fast", "build", a.build_target]
    else:
        target = (project / a.file).resolve()
        if not target.is_relative_to(project) or target.suffix != ".lean" or not target.is_file():
            p.error("The target must be one existing Lean file inside this project.")
        command = [lake, "env", "lean", "--threads=1", "--memory=2048"]
        if a.emit:
            out = project / ".lake" / "build" / "lib" / "lean" / target.relative_to(project).with_suffix(".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            command.extend(["-o", str(out)])
        command.append(str(target))
    return run_job(command,
                   project, log, 6144, a.timeout, env_overrides=child_env)

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError) as e:
        print(f"GUARD: {e}", file=sys.stderr)
        raise SystemExit(75)
