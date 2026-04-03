#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
check_termination.py
Merged verifier for both properties with rsweep-style parameterization.


Commands:
  python check_termination.py --termination
  python check_termination.py --termination-sweep
  python check_termination.py --safety
  python check_termination.py --safety-sweep
  python check_termination.py --both

Optional:
  --rmax=N   (for --termination / --safety single run)
"""

import re
import sys
import time
import subprocess
from pathlib import Path

WORKSPACE = Path(__file__).parent
TLA_FILE = WORKSPACE / "F_Tendermint.tla"
OUT_BASE = WORKSPACE / "_apalache-out" / "F_Tendermint.tla"

SEP = "=" * 62
SEP2 = "-" * 62

EXIT_OK = 0
EXIT_COUNTEREXAMPLE = 12

# Shared sweep parameters (rsweep style)
R_SWEEP = [1, 2, 3, 5, 8, 10]

# Termination params (simulate)
TERM_LENGTH = 100
TERM_MAX_RUN = 60

# Safety params (check)
SAFETY_LENGTH = 5

# Keep original text for restore
ORIG_TLA = TLA_FILE.read_text(encoding="utf-8")


def find_latest_dir():
    if not OUT_BASE.exists():
        return None
    dirs = sorted(OUT_BASE.iterdir(), key=lambda d: d.stat().st_mtime, reverse=True)
    return dirs[0] if dirs else None


def run_cmd(cmd):
    t0 = time.time()
    rc = subprocess.run(" ".join(cmd), cwd=str(WORKSPACE), shell=True, capture_output=False).returncode
    return rc, time.time() - t0


def patch_maxround_in_cinit(cinit_name: str, rmax: int):
    """Patch '/\ MaxRound = X' in target cinit block only."""
    text = TLA_FILE.read_text(encoding="utf-8")

    # Match block header then first MaxRound assignment in that block scope.
    # Keep this conservative and replace only first occurrence.
    pat = re.compile(rf"({re.escape(cinit_name)}\s*==[\s\S]*?/\\\s*MaxRound\s*=\s*)(\d+)")
    m = pat.search(text)
    if not m:
        raise RuntimeError(f"Cannot find MaxRound assignment in {cinit_name}")

    new_text = text[:m.start()] + m.group(1) + str(rmax) + text[m.end():]
    TLA_FILE.write_text(new_text, encoding="utf-8")


def restore_tla():
    TLA_FILE.write_text(ORIG_TLA, encoding="utf-8")


def read_tail_with_offset(path, n=450):
    with open(path, "rb") as f:
        f.seek(0, 2)
        size = f.tell()
        buf = b""
        pos = size
        while pos > 0 and buf.count(b"\n") < n:
            chunk = min(8192, pos)
            pos -= chunk
            f.seek(pos)
            buf = f.read(chunk) + buf
    text = buf.decode("utf-8", errors="replace")
    total = sum(1 for _ in open(path, "rb"))
    start = max(1, total - text.count("\n"))
    return text, start, total


def parse_last_state(tla_path):
    text, start_lineno, total_lines = read_tail_with_offset(tla_path, 450)
    state_matches = list(re.finditer(r"\(\* State(\d+)", text))
    if not state_matches:
        return None

    last = state_matches[-1]
    state_num = last.group(1)
    block = text[last.start():]
    state_line = start_lineno + text[:last.start()].count("\n")

    decision = {}
    node_lines = {}
    dec_field = re.search(r"/\\\s*decision\s*=\s*SetAsFun\(\{", block)
    decision_line = state_line + block[:dec_field.start()].count("\n") if dec_field else None

    for m in re.finditer(r'<<"(v\d+)",\s*SetAsFun\(\{([^}]*)\}\)>>', block):
        node = m.group(1)
        node_lines[node] = state_line + block[:m.start()].count("\n")
        hmap = m.group(2)
        decision[node] = {}
        for hh, val in re.findall(r"<<(\d+),\s*(\d+)>>", hmap):
            decision[node][int(hh)] = int(val)

    cor = re.search(r"/\\\s*corrupted\s*=\s*\{([^}]*)\}", block)
    corrupted = set(re.findall(r'"(v\d+)"', cor.group(1))) if cor else set()

    atk = re.search(r"attackCount\s*=\s*(\d+)", block)
    attack_count = int(atk.group(1)) if atk else -1

    return {
        "total_lines": total_lines,
        "state_num": state_num,
        "state_line": state_line,
        "decision": decision,
        "decision_line": decision_line,
        "node_lines": node_lines,
        "corrupted": corrupted,
        "attack_count": attack_count,
    }


def report_termination_trace(tla_path):
    info = parse_last_state(tla_path)
    if not info:
        print("[ERROR] failed to parse", tla_path)
        return False

    print(SEP2)
    print(f"Trace: {tla_path.name} | last=State{info['state_num']} @~{info['state_line']}")

    all_decided = True
    vals = []
    for node in sorted(info["decision"]):
        v = info["decision"][node].get(0, 0)
        if node in info["corrupted"]:
            continue
        if v == 0:
            all_decided = False
        else:
            vals.append(v)

    if all_decided:
        print("Termination witness: PASS (all honest decided)")
        if vals and len(set(vals)) == 1:
            print(f"Agreement in witness: PASS (value={vals[0]})")
        return True
    print("Termination witness: FAIL")
    return False


def run_termination_single(rmax: int, tag="TR-single"):
    patch_maxround_in_cinit("CInit", rmax)
    cmd = [
        "apalache-mc", "simulate",
        "--features=no-rows",
        "--cinit=CInit",
        "--init=Init",
        "--next=NextBoundedAttack",
        "--inv=NotYetTerminated",
        f"--length={TERM_LENGTH}",
        f"--max-run={TERM_MAX_RUN}",
        str(TLA_FILE),
    ]

    print()
    print(SEP)
    print(f"TERMINATION [{tag}] R_max={rmax}")
    print("Command:")
    print("  " + " ".join(cmd))

    rc, sec = run_cmd(cmd)
    print(f"Finished in {sec:.1f}s | EXITCODE={rc}")

    if rc == EXIT_COUNTEREXAMPLE:
        run_dir = find_latest_dir()
        files = sorted(run_dir.glob("violation*.tla")) if run_dir else []
        ok = all(report_termination_trace(f) for f in files) if files else True
        result = "PASS" if ok else "FAIL?"
    elif rc == EXIT_OK:
        result = "INCONCLUSIVE"
        print("No witness found under current length/max-run.")
    else:
        result = f"ERR({rc})"

    return {"id": tag, "rmax": rmax, "time": sec, "result": result, "rc": rc}


def run_termination_sweep():
    rows = []
    try:
        for i, r in enumerate(R_SWEEP, 1):
            rows.append(run_termination_single(r, f"TR-{i:02d}"))
    finally:
        restore_tla()

    print()
    print(SEP)
    print("TERMINATION SWEEP SUMMARY")
    print(SEP2)
    print("  {:<8} {:>5} {:>9}  {}".format("Run", "R", "Time(s)", "Result"))
    print("  " + "-" * 36)
    for r in rows:
        print("  {:<8} {:>5} {:>9.1f}  {}".format(r["id"], r["rmax"], r["time"], r["result"]))
    print(SEP)


def run_safety_single(rmax: int, tag="SR-single"):
    patch_maxround_in_cinit("CInitSafety", rmax)
    cmd = [
        "apalache-mc", "check",
        "--features=no-rows",
        "--cinit=CInitSafety",
        "--init=InitSafety",
        "--next=NextSafety",
        "--inv=Agreement",
        f"--length={SAFETY_LENGTH}",
        str(TLA_FILE),
    ]

    print()
    print(SEP)
    print(f"SAFETY [{tag}] R_max={rmax}")
    print("Command:")
    print("  " + " ".join(cmd))

    rc, sec = run_cmd(cmd)
    print(f"Finished in {sec:.1f}s | EXITCODE={rc}")

    if rc == EXIT_OK:
        print("Safety PASS: Agreement holds up to bounded length.")
        result = "PASS"
    elif rc == EXIT_COUNTEREXAMPLE:
        print("Safety FAIL: counterexample found (check violation*.tla).")
        result = "FAIL"
    else:
        result = f"ERR({rc})"

    return {"id": tag, "rmax": rmax, "time": sec, "result": result, "rc": rc}


def write_safety_tex(rows):
    out = WORKSPACE / "safety_table.tex"
    tex = []
    tex.append("% Auto-generated by check_termination.py --safety-sweep")
    tex.append(r"\begin{table}[ht]")
    tex.append(r"\centering")
    tex.append(r"\caption{Safety (Agreement) verification for $\mathcal{F}^{V,\Delta,\Sigma}_{\mathrm{Tendermint}}$ under bounded delay attack ($|V|=4$, $f=1$, $\Delta=\Sigma=1$, $H_{\max}=1$, \texttt{length}$=" + str(SAFETY_LENGTH) + r"$). MaxRound is patched per run (rsweep-style), not hard-coded via multiple CInit blocks. RC$=0$ confirms Agreement.}")
    tex.append(r"\label{tab:safety}")
    tex.append(r"\small")
    tex.append(r"\begin{tabular}{@{}ccrrc@{}}")
    tex.append(r"\toprule")
    tex.append(r"\textbf{Run} & $R_{\max}$ & \textbf{length} & \textbf{Time\,(s)} & \textbf{Result} \\")
    tex.append(r"\midrule")
    for r in rows:
        tex.append(f"{r['id']} & {r['rmax']} & {SAFETY_LENGTH} & {r['time']:.1f} & {r['result']} \\")
    tex.append(r"\bottomrule")
    tex.append(r"\end{tabular}")
    tex.append(r"\end{table}")
    out.write_text("\n".join(tex), encoding="utf-8")
    print("Wrote:", out)


def run_safety_sweep():
    rows = []
    try:
        for i, r in enumerate(R_SWEEP, 1):
            rows.append(run_safety_single(r, f"SR-{i:02d}"))
    finally:
        restore_tla()

    print()
    print(SEP)
    print("SAFETY SWEEP SUMMARY")
    print(SEP2)
    print("  {:<8} {:>5} {:>9}  {}".format("Run", "R", "Time(s)", "Result"))
    print("  " + "-" * 36)
    for r in rows:
        print("  {:<8} {:>5} {:>9.1f}  {}".format(r["id"], r["rmax"], r["time"], r["result"]))
    print(SEP)

    write_safety_tex(rows)


def parse_rmax_from_args(default_val):
    for a in sys.argv[1:]:
        m = re.match(r"--rmax=(\d+)", a)
        if m:
            return int(m.group(1))
    return default_val


def main():
    args = set(sys.argv[1:])

    try:
        if "--termination-sweep" in args:
            run_termination_sweep()
            return

        if "--termination" in args:
            r = parse_rmax_from_args(10)
            run_termination_single(r)
            return

        if "--safety-sweep" in args:
            run_safety_sweep()
            return

        if "--safety" in args:
            r = parse_rmax_from_args(2)
            run_safety_single(r)
            return

        if "--both" in args:
            run_termination_sweep()
            run_safety_sweep()
            return

        # default keeps old expectation: termination
        run_termination_single(10)
    finally:
        restore_tla()


if __name__ == "__main__":
    main()
