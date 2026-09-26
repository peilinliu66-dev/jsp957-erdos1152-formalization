#!/usr/bin/env python3
"""Build the existing pinned JSP957 proof chain and record genuine outputs.

python3 scripts/build_v6.py --cache    # explicitly retrieve the pinned caches
python3 scripts/build_v6.py            # dependencies already installed

Execution is synchronous. No public writes, login, remote proof service,
subagent, or scheduled task is used. Missing Lake is exit 127, never a pass.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.33.0"
VERSION = "4.33.0"
MATHLIB = "db584cd6d46c92f209a44c0f1c829460d327499d"
THEOREM = "Erdos1152.V5.ae_limsup_eq_top"
STRICT_EPSILON_THEOREM = "Erdos1152.V5.ae_limsup_eq_top_strict_epsilon"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STAGES = [
    ("fejer-grid", ["+Erdos1152.V5.FejerGrid"]),
    ("baseline-coarse-v3-v4", ["Erdos1152", "JSP957V3", "+Erdos1152.CoarseMain",
                               "JSP957V4High", "JSP957V4"]),
    ("small-scale-field", ["JSP957V5Field"]),
    ("bernstein", ["JSP957V5Bernstein"]),
    ("sampling", ["JSP957V5Sampling"]),
    ("weighted-family", ["JSP957V5Weighted"]),
    ("complete-final", ["JSP957V5", "JSP957Final"]),
]
CHECKS = [
    ("fejer-regression", "checks/FejerGridRegression.lean"),
    ("repair-declarations", "checks/V6Repairs.lean"),
    ("analytic-declarations", "checks/V5.lean"),
    ("final-statement", "checks/FinalStatement.lean"),
    ("final-axioms", "checks/FinalAxioms.lean"),
    ("strict-epsilon-statement", "checks/StrictEpsilonStatement.lean"),
    ("strict-epsilon-axioms", "checks/StrictEpsilonAxioms.lean"),
]


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def source_hashes() -> dict[str, str]:
    files = [p for p in ROOT.rglob("*.lean")
             if ".lake" not in p.parts and ".git" not in p.parts]
    files += [ROOT / f for f in ("lean-toolchain", "lakefile.toml", "lakefile.lean",
                                "lake-manifest.json", "scripts/build_v6.py",
                                "scripts/build_v6.sh", "scripts/static_v6.py")]
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(files) if p.is_file()}


def parse_axioms(output: str, name: str) -> set[str] | None:
    """Accept only an axiom line belonging to this exact declaration."""
    qname = re.escape(name)
    pattern = rf"^['\"]?{qname}['\"]?\s+depends on axioms:\s*\[([^\]]*)\]"
    m = re.search(pattern, output, flags=re.M)
    if m:
        return {a.strip() for a in m.group(1).split(",") if a.strip()}
    if re.search(rf"^['\"]?{qname}['\"]?\s+does not depend on any axioms\s*$", output, re.M):
        return set()
    return None


def has_hole_output(output: str) -> bool:
    return bool(re.search(r"\bsorryAx\b|declaration uses ['\"]sorry['\"]", output))


def stop_process_group(proc: subprocess.Popen) -> None:
    """Stop the command and inherited compiler process group, retaining pipes."""
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        proc.wait(timeout=3)
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    proc.wait()


def capture_process(command: list[str], cwd: Path, path: Path,
                    timeout: float | None = None, interrupt_signal=None) -> tuple[int, bytes, str]:
    """Capture genuine merged output through PIPE and atomically refresh its path.

    A workspace may replace an open log pathname while a process is running.
    Reading the original pipe into memory and replacing fresh snapshots avoids
    losing the later bytes in an unlinked, long-open log file. The returned raw
    bytes, not a later filesystem read, are the verification parser's input.
    Driver diagnostics are separate metadata and never added to compiler output.
    """
    captured = bytearray()
    mutex = threading.Lock()
    reader_errors: list[str] = []
    proc = None
    reader = None
    note = ""

    def drain(pipe) -> None:
        try:
            while chunk := pipe.read(65536):
                with mutex:
                    captured.extend(chunk)
        except OSError as error:
            reader_errors.append(f"{type(error).__name__}: {error}")
        finally:
            pipe.close()

    def snapshot() -> bytes:
        with mutex:
            raw = bytes(captured)
        temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
        temporary.write_bytes(raw)
        temporary.replace(path)
        return raw

    try:
        proc = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, start_new_session=True, bufsize=0)
        assert proc.stdout is not None
        reader = threading.Thread(target=drain, args=(proc.stdout,), daemon=True)
        reader.start()
        deadline = time.monotonic() + timeout if timeout else None
        while proc.poll() is None or reader.is_alive():
            remaining = deadline - time.monotonic() if deadline is not None else None
            if remaining is not None and remaining <= 0:
                raise subprocess.TimeoutExpired(command, timeout)
            snapshot()
            interval = min(1.0, remaining) if remaining is not None else 1.0
            if proc.poll() is None:
                try:
                    proc.wait(timeout=interval)
                except subprocess.TimeoutExpired:
                    pass
            else:
                reader.join(timeout=interval)
        code = proc.wait()
    except subprocess.TimeoutExpired:
        assert proc is not None
        stop_process_group(proc)
        code = 124
        note = "Command timeout; stopped process group; retained actual pipe output."
    except KeyboardInterrupt:
        if proc is not None:
            stop_process_group(proc)
        code = 128 + (interrupt_signal() if interrupt_signal else signal.SIGINT)
        note = "Interrupted; stopped process group; retained actual pipe output."
    except OSError as error:
        if proc is not None:
            stop_process_group(proc)
        code = 127 if isinstance(error, FileNotFoundError) else 126
        note = f"{type(error).__name__}: {error}"
    finally:
        if reader is not None:
            reader.join()
        raw = snapshot()
    if reader_errors:
        code = 74
        note = "Pipe capture failed: " + "; ".join(reader_errors)
    return code, raw, note


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--cache", action="store_true")
    ap.add_argument("--timeout-seconds", type=int, default=0,
                    help="Per command; 0 means no script timeout.")
    args = ap.parse_args()
    if args.timeout_seconds < 0:
        ap.error("timeout must be nonnegative")
    # A new run directory keeps every earlier log intact.
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
    logs = ROOT / "logs" / "v6" / stamp
    logs.mkdir(parents=True, exist_ok=False)
    receipt: dict[str, Any] = {
        "started_utc": utc(), "status": "RUNNING", "exit_code": None,
        "driver_argv": [sys.executable, *sys.argv],
        "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "lean_toolchain": TOOLCHAIN, "mathlib_commit": MATHLIB,
        "source_theorem_name": THEOREM, "source_sha256_at_attempt": source_hashes(),
        "strict_epsilon_theorem_name": STRICT_EPSILON_THEOREM,
        "strict_epsilon_statement_output": "NOT_RUN", "strict_epsilon_axioms_output": "NOT_RUN",
        "strict_epsilon_kernel_verified": False,
        "environment": {k: shutil.which(k) for k in ("lean", "lake", "elan", "git")},
        "commands": [], "planned_build_stages": STAGES, "planned_checks": CHECKS,
        "first_failed_command": None, "first_actual_compiler_error": None,
        "elaborator": "NOT_STARTED", "kernel": "NOT_STARTED",
        "final_statement_output": "NOT_RUN", "final_axioms_output": "NOT_RUN",
        "unconditional_theorem_kernel_verified": False,
        "verified_original_terminal_inputs_eliminated": 0,
        "dependency_inventory_before": [], "dependency_inventory_after": [],
        "dependency_tree_clean": False, "interrupted_signal": None,
        "scope_note": "Static source repairs and diagnostic targets are not full theorem verification.",
        "run_directory": logs.relative_to(ROOT).as_posix(),
    }

    def save_receipt() -> None:
        content = json.dumps(receipt, ensure_ascii=False, indent=2) + "\n"
        for path in (logs / "BUILD_RESULT.json", ROOT / "logs/v6/BUILD_RESULT_V6.json"):
            temporary = path.with_name(path.name + f".{stamp}.tmp")
            temporary.write_text(content, encoding="utf-8")
            temporary.replace(path)

    def finish(status: str, code: int, message: str = "") -> int:
        after = source_hashes()
        if code == 0 and after != receipt["source_sha256_at_attempt"]:
            status, code = "SOURCE_CHANGED_DURING_BUILD", 7
            receipt["unconditional_theorem_kernel_verified"] = False
            receipt["strict_epsilon_kernel_verified"] = False
            receipt["verified_original_terminal_inputs_eliminated"] = 0
        if receipt["interrupted_signal"] is not None:
            status, code = "INTERRUPTED", 128 + receipt["interrupted_signal"]
        if code:
            receipt["unconditional_theorem_kernel_verified"] = False
            receipt["strict_epsilon_kernel_verified"] = False
            receipt["verified_original_terminal_inputs_eliminated"] = 0
        receipt.update(status=status, exit_code=code, finished_utc=utc(), message=message,
                       source_sha256_at_finish=after,
                       source_unchanged_during_attempt=(after == receipt["source_sha256_at_attempt"]))
        save_receipt()
        print(f"V6_BUILD_STATUS={status}\nEXIT_CODE={code}", flush=True)
        return code

    def interrupt(signum: int, _frame: Any) -> None:
        receipt["interrupted_signal"] = signum
        raise KeyboardInterrupt

    signal.signal(signal.SIGINT, interrupt)
    signal.signal(signal.SIGTERM, interrupt)
    save_receipt()

    def run(label: str, command: list[str], *, command_timeout: int | None = None) -> tuple[int, str]:
        begin, tick = utc(), time.monotonic()
        path = logs / (label + ".log")
        receipt["active_command"] = {"name": label, "argv": command,
                                     "log": path.relative_to(ROOT).as_posix()}
        save_receipt()
        code, raw_output, driver_note = capture_process(
            command, ROOT, path, command_timeout or args.timeout_seconds or None,
            lambda: receipt["interrupted_signal"] or signal.SIGINT)
        output = raw_output.decode("utf-8", errors="replace")
        item = {"name": label, "argv": command, "cwd": str(ROOT),
                "started_utc": begin, "finished_utc": utc(),
                "wall_seconds": time.monotonic() - tick, "exit_code": code,
                "log": path.relative_to(ROOT).as_posix(),
                "log_sha256": hashlib.sha256(raw_output).hexdigest(),
                "captured_output_bytes": len(raw_output),
                "capture_method": "PIPE with reader thread and atomic log snapshots",
                "driver_note": driver_note}
        receipt["commands"].append(item)
        if code and receipt["first_failed_command"] is None:
            receipt["first_failed_command"] = item
        # Preserve exact raw context, without claiming every Lake error is an elaboration error.
        if receipt["first_actual_compiler_error"] is None:
            m = re.search(r"(?m)^(?:.*\.lean:\d+:\d+:\s*error:.*|error:.*\.lean:\d+:\d+:.*)$", output)
            if m:
                receipt["first_actual_compiler_error"] = {"line": m.group(0), "log": item["log"]}
        receipt["active_command"] = None
        save_receipt()
        print(f"{label}: exit {code}; {item['log']}", flush=True)
        return code, output

    def dependencies(packages: list[dict[str, Any]], phase: str) -> list[dict[str, Any]]:
        inventory = []
        git = receipt["environment"]["git"]
        for package in packages:
            name = package.get("name", "")
            if not re.fullmatch(r"[A-Za-z0-9_.-]+", name):
                inventory.append({"name": name, "error": "Invalid package name"})
                continue
            path = ROOT / ".lake/packages" / name
            item = {"name": name, "manifest_revision": package.get("rev"),
                    "path": str(path), "resolved_path": str(path.resolve()),
                    "present": path.is_dir(), "head_matches": False, "clean": False}
            if git and path.is_dir() and package.get("type") == "git":
                code, head = run(f"{phase}-{name}-head", [git, "-C", str(path),
                                                          "rev-parse", "HEAD"], command_timeout=30)
                item.update(head=head.strip(), head_exit_code=code,
                            head_matches=(code == 0 and head.strip() == package.get("rev")))
                code, status = run(f"{phase}-{name}-status", [git, "-C", str(path), "status",
                                     "--porcelain=v1", "--untracked-files=all"], command_timeout=30)
                item.update(status_exit_code=code, status_porcelain=status,
                            clean=(code == 0 and not status.strip()))
            else:
                item["error"] = "Git checkout or git executable unavailable"
            inventory.append(item)
            if receipt["interrupted_signal"] is not None:
                break
        return inventory

    def execute() -> int:
        try:
            if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
                return finish("PIN_MISMATCH", 2, "lean-toolchain mismatch")
            manifest = json.loads((ROOT / "lake-manifest.json").read_text())
            packages = manifest.get("packages", [])
            ms = [p for p in packages if p.get("name") == "mathlib"]
            if len(ms) != 1 or ms[0].get("rev") != MATHLIB:
                return finish("PIN_MISMATCH", 2, "mathlib manifest revision mismatch")
        except (OSError, ValueError) as exc:
            return finish("PIN_READ_ERROR", 2, str(exc))

        if not packages or len({p.get("name") for p in packages}) != len(packages):
            return finish("PIN_MISMATCH", 2, "Missing or duplicate dependency manifest entries")
        inventory = dependencies(packages, "dependencies-before")
        receipt["dependency_inventory_before"] = inventory
        receipt["dependency_tree_clean"] = all(p.get("clean") for p in inventory)
        receipt["dependency_policy"] = (
            "Report all tracked/untracked differences without changing dependency sources. "
            "Dirty exact-revision trees may be built for diagnostics, but cannot earn final verification.")
        if receipt["interrupted_signal"] is not None:
            return finish("INTERRUPTED", 130)

        lake = receipt["environment"]["lake"]
        if lake is None:
            text = "BUILD_NOT_RUN: lake executable was not found.\nEXIT_CODE=127\n"
            (logs / "build-attempt.txt").write_text(text, encoding="utf-8")
            print(text, end="", flush=True)
            return finish("UNCOMPILED", 127, "No Lean build/check command was executed.")

        if any(p.get("present") and not p.get("head_matches") for p in inventory):
            return finish("DEPENDENCY_REVISION_UNVERIFIED", 2,
                          "Existing dependency checkout differs from its pinned revision or cannot be read.")
        if any(not p.get("present") for p in inventory) and not args.cache:
            return finish("DEPENDENCIES_INCOMPLETE", 2,
                          "Dependency checkout missing; automatic dependency retrieval was not requested.")

        code, output = run("toolchain-version", [lake, "env", "lean", "--version"])
        if code:
            return finish("UNCOMPILED_TOOLCHAIN_ERROR", code)
        receipt["actual_toolchain_output"] = output
        m = re.search(r"^Lean \(version\s+([^,\s)]+)", output, re.M)
        if not m or m.group(1) != VERSION:
            return finish("TOOLCHAIN_VERSION_MISMATCH", 2, "Require exact 4.33.0, not rc/nightly/other patch.")
        if args.cache:
            code, _ = run("cache-get", [lake, "exe", "cache", "get"])
            if code:
                return finish("DEPENDENCIES_INCOMPLETE", code)

            inventory = dependencies(packages, "dependencies-after-cache")
            receipt["dependency_inventory_after_cache"] = inventory
            if any(not p.get("head_matches") for p in inventory):
                return finish("DEPENDENCY_REVISION_UNVERIFIED", 2)
            receipt["dependency_tree_clean"] = (
                all(not p.get("present") or p.get("clean")
                    for p in receipt["dependency_inventory_before"])
                and all(p.get("clean") for p in inventory))

        from static_v6 import inspect
        static_report = inspect(ROOT)
        (logs / "static-before-build.json").write_text(
            json.dumps(static_report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        receipt["static_report"] = (logs / "static-before-build.json").relative_to(ROOT).as_posix()
        if static_report["has_blocking_findings"]:
            return finish("STATIC_SOURCE_FINDINGS", 4,
                          "See static report; this is not a Lean compiler result.")

        for label, targets in STAGES:
            receipt["elaborator"] = "BUILD_INVOKED_NOT_YET_CONFIRMED"
            code, output = run(label, [lake, "build", *targets])
            if code:
                return finish("BUILD_FAILED", code)
            if has_hole_output(output):
                return finish("SORRY_FOUND_IN_BUILD", 4)
            if label == "fejer-grid":
                code, output = run("fejer-regression", [lake, "env", "lean", CHECKS[0][1]])
                if code or has_hole_output(output):
                    return finish("REGRESSION_FAILED", code or 4)
        receipt["elaborator"] = "FULL_BUILD_COMPLETED"
        receipt["kernel"] = "LEAN_BUILD_SUCCEEDED_NOT_INDEPENDENTLY_RECHECKED"
        for label, path in CHECKS[1:]:
            code, output = run(label, [lake, "env", "lean", path])
            if code:
                return finish("DECLARATION_CHECK_FAILED", code)
            if has_hole_output(output):
                return finish("SORRY_AXIOM_FOUND", 4)
            logfile = receipt["commands"][-1]["log"]
            if label == "final-statement":
                receipt["final_statement_output"] = logfile
                if THEOREM not in output:
                    return finish("FINAL_STATEMENT_NOT_FOUND", 5)
            elif label == "final-axioms":
                receipt["final_axioms_output"] = logfile
                axioms = parse_axioms(output, THEOREM)
                if axioms is None:
                    return finish("AXIOMS_OUTPUT_UNRECOGNIZED", 5)
                receipt["final_axioms"] = sorted(axioms)
                if axioms - ALLOWED_AXIOMS:
                    receipt["unexpected_axioms"] = sorted(axioms - ALLOWED_AXIOMS)
                    return finish("UNEXPECTED_AXIOMS", 6)
            elif label == "strict-epsilon-statement":
                receipt["strict_epsilon_statement_output"] = logfile
                if STRICT_EPSILON_THEOREM not in output:
                    return finish("STRICT_EPSILON_STATEMENT_NOT_FOUND", 5)
            elif label == "strict-epsilon-axioms":
                receipt["strict_epsilon_axioms_output"] = logfile
                axioms = parse_axioms(output, STRICT_EPSILON_THEOREM)
                if axioms is None:
                    return finish("STRICT_EPSILON_AXIOMS_OUTPUT_UNRECOGNIZED", 5)
                receipt["strict_epsilon_axioms"] = sorted(axioms)
                if axioms - ALLOWED_AXIOMS:
                    receipt["strict_epsilon_unexpected_axioms"] = sorted(axioms - ALLOWED_AXIOMS)
                    return finish("STRICT_EPSILON_UNEXPECTED_AXIOMS", 6)
        after = dependencies(packages, "dependencies-after")
        receipt["dependency_inventory_after"] = after
        if any(not p.get("head_matches") for p in after):
            return finish("DEPENDENCY_REVISION_CHANGED_DURING_BUILD", 8)
        if not receipt["dependency_tree_clean"] or any(not p.get("clean") for p in after):
            return finish("BUILD_PASSED_DEPENDENCY_TREE_DIRTY", 8,
                          "Lean commands succeeded, but dependency differences prevent pinned-tree verification.")
        receipt["kernel"] = "FINAL_THEOREM_ACCEPTED_BY_LEAN_STANDARD_AXIOMS"
        receipt["unconditional_theorem_kernel_verified"] = True
        receipt["strict_epsilon_kernel_verified"] = True
        receipt["verified_original_terminal_inputs_eliminated"] = 3
        return finish("FULL_FINAL_ELABORATED_STANDARD_AXIOMS", 0)

    try:
        return execute()
    except KeyboardInterrupt:
        receipt["interrupted_signal"] = receipt["interrupted_signal"] or signal.SIGINT
        return finish("INTERRUPTED", 130)
    except Exception as exc:
        return finish("DRIVER_ERROR", 70, f"{type(exc).__name__}: {exc}")


if __name__ == "__main__":
    sys.exit(main())
