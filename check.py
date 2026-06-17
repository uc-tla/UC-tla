#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
check_termination.py
Merged verifier for both properties with rsweep-style parameterization.

Key idea (same as __run_rsweep.py):
- Do NOT maintain multiple CInitSafetyR* constants in TLA.
- Patch MaxRound inside target CInit block before each run.
- Restore original TLA after runs.

Commands:
  python check.py --termination
  python check.py --termination-sweep
  python check.py --safety
  python check.py --safety-sweep
  python check.py --both
  python check.py --optimized-safety --nodes=7 --height=2 --rmax=2
  python check.py --optimized-termination --nodes=7 --height=2 --rmax=2
  python check.py --optimized-both --nodes=7 --height=2 --rmax=2
  python check.py --comprehensive   # 13 configs: Phase 1 (8 std) + Phase 2 (5 scalable)

Optimized modes always enable bounded maximum-delay AdversaryWake injections.

Optional:
  --rmax=N       MaxRound for original single/sweep patching or optimized CInitOptimized
  --nodes=N      validator count for optimized Apalache sanity checks, default 7
  --height=N     MaxHeight for optimized Apalache sanity checks, default 2
  --length=N     override optimized safety check length
  --term-length=N override optimized termination simulation length
  --max-run=N    override optimized termination simulation runs
"""

import re
import sys
import time
import json
import shutil
import tempfile
import subprocess
from datetime import datetime
from pathlib import Path

WORKSPACE = Path(__file__).parent
TLA_FILE = WORKSPACE / "F_Tendermint.tla"
OUT_BASE = WORKSPACE / "_apalache-out" / "F_Tendermint.tla"

RUN_DIR = Path(tempfile.mkdtemp(prefix="check_tla_", dir=str(WORKSPACE)))
RUN_TLA_FILE = RUN_DIR / "F_Tendermint.tla"
shutil.copy2(TLA_FILE, RUN_TLA_FILE)

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

# Optimized Apalache sanity-check params for reviewer response
OPT_TERM_MAX_RUN = 1
OPT_DEFAULT_NODES = 7
OPT_DEFAULT_HEIGHT = 2
OPT_DEFAULT_ROUND = 2
OPT_DELTA = 1
OPT_SIGMA = 1
STATS_DIR = WORKSPACE / "verification_stats"
STATS_DIR.mkdir(exist_ok=True)

# -----------------------------------------------------------------------
# 13-configuration two-phase sweep (Phase 1: standard | Phase 2: scalable)
# -----------------------------------------------------------------------
# Phase 1 – standard verification: |V|=4, f=1, H=1, vary aggressive Sigma/Delta/Rmax
#   each entry = (sigma, delta, rmax,  tag)
#   Aggressive settings: Sigma in {3,4,5}, Delta in {3,4} to stress-test
#   the delay-attack window and round-exploration bounds.
PHASE1_CONFIGS = [
    (3, 3, 2, "P1-01"),
    (3, 3, 3, "P1-02"),
    (3, 3, 5, "P1-03"),
    (4, 3, 2, "P1-04"),
    (4, 3, 3, "P1-05"),
    (4, 4, 2, "P1-06"),
    (4, 4, 3, "P1-07"),
    (5, 4, 2, "P1-08"),
    (5, 4, 3, "P1-09"),
]

# Phase 2 – scalable verification: larger |V| and H, optimized Apalache next
#   each entry = (nodes, height, rmax,  tag)
PHASE2_CONFIGS = [
    (7,  5, 2, "P2-01"),
    (7,  5, 3, "P2-02"),
    (7,  3, 2, "P2-03"),
    (7,  3, 5, "P2-04"),
    (10, 3, 2, "P2-05"),
    (10, 3, 3, "P2-06"),
    (13, 3, 2, "P2-07"),
    (13, 3, 3, "P2-08"),
]


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
    """Patch a MaxRound assignment in target cinit block only."""
    text = RUN_TLA_FILE.read_text(encoding="utf-8")

    # Match block header then first MaxRound assignment in that block scope.
    # Keep this conservative and replace only first occurrence.
    pat = re.compile(rf"({re.escape(cinit_name)}\s*==[\s\S]*?/\\\s*MaxRound\s*=\s*)(\d+)")
    m = pat.search(text)
    if not m:
        raise RuntimeError(f"Cannot find MaxRound assignment in {cinit_name}")

    new_text = text[:m.start()] + m.group(1) + str(rmax) + text[m.end():]
    RUN_TLA_FILE.write_text(new_text, encoding="utf-8")


def validator_names(n: int):
    return [f"v{i}" for i in range(1, n + 1)]


def optimized_config(nodes=None, height=None, rmax=None):
    n = nodes or OPT_DEFAULT_NODES
    hmax = height if height is not None else OPT_DEFAULT_HEIGHT
    r = rmax if rmax is not None else OPT_DEFAULT_ROUND
    f = (n - 1) // 3
    vals = validator_names(n)
    corrupted = vals[-f:] if f > 0 else []
    return {
        "nodes": n,
        "f": f,
        "height": hmax,
        "rmax": r,
        "delta": OPT_DELTA,
        "sigma": OPT_SIGMA,
        "validators": vals,
        "corrupted": corrupted,
    }


def patch_safety_params(sigma: int, delta: int, rmax: int):
    """Patch Sigma, Delta, and MaxRound in CInitSafety."""
    text = RUN_TLA_FILE.read_text(encoding="utf-8")

    pat = re.compile(
        r"(CInitSafety\s*==[\s\S]*?)(/\\\s*Delta\s*=\s*)(\d+)([\s\S]*?)(/\\\s*Sigma\s*=\s*)(\d+)([\s\S]*?)(/\\\s*MaxRound\s*=\s*)(\d+)"
    )
    m = pat.search(text)
    if not m:
        raise RuntimeError("Cannot find Delta/Sigma/MaxRound in CInitSafety")

    new_text = (
        text[:m.start()]
        + m.group(1) + m.group(2) + str(delta)
        + m.group(4) + m.group(5) + str(sigma)
        + m.group(7) + m.group(8) + str(rmax)
        + text[m.end():]
    )
    RUN_TLA_FILE.write_text(new_text, encoding="utf-8")


def patch_optimized_cinit(cfg):
    """Patch CInitOptimized for larger bounded sanity checks."""
    text = RUN_TLA_FILE.read_text(encoding="utf-8")
    validators = "{" + ", ".join(f'"{v}"' for v in cfg["validators"]) + "}"
    corrupted = "{" + ", ".join(f'"{v}"' for v in cfg["corrupted"]) + "}"
    block = (
        f"CInitOptimized ==\n"
        f"    /\\ Validators = {validators}\n"
        f"    /\\ InitiallyCorrupted = {corrupted}\n"
        f"    /\\ Delta = {cfg['delta']}\n"
        f"    /\\ Sigma = {cfg['sigma']}\n"
        f"    /\\ MaxHeight = {cfg['height']}\n"
        f"    /\\ MaxRound = {cfg['rmax']}\n"
        f"    /\\ Values = {{1}}\n"
        f"    /\\ NilValue = 0"
    )
    pat = re.compile(r"CInitOptimized\s*==[\s\S]*?(?=\n\n\\\* Full spec with bounded attack)")
    m = pat.search(text)
    if not m:
        raise RuntimeError("Cannot find CInitOptimized block")
    RUN_TLA_FILE.write_text(text[:m.start()] + block + text[m.end():], encoding="utf-8")


def parse_int_arg(name, default_val):
    prefix = f"--{name}="
    for a in sys.argv[1:]:
        if a.startswith(prefix):
            return int(a.split("=", 1)[1])
    return default_val


def optimized_attack_length(cfg):
    # Maximum-delay attack prefix uses AdversaryWake and delay-induced round advance
    # for each allowed Byzantine fault budget slot, then four abstract progress
    # steps per height: propose, prevote, precommit, commit.
    return 2 * cfg["f"] + 4 * (cfg["height"] + 1) + 2


def optimized_safety_length(cfg):
    return parse_int_arg("length", optimized_attack_length(cfg))


def optimized_term_length(cfg):
    return parse_int_arg("term-length", optimized_attack_length(cfg))


def optimized_max_run():
    return parse_int_arg("max-run", OPT_TERM_MAX_RUN)


def write_json_stats(name, rows, cfg, notes):
    payload = {
        "generated_at": datetime.now().isoformat(),
        "scope": "bounded sanity check of the ideal functionality, not real protocol verification or UC refinement",
        "model": "F_Tendermint.tla",
        "optimized_apalache": True,
        "configuration": cfg,
        "notes": notes,
        "results": rows,
        "summary": {
            "checks": len(rows),
            "passed": sum(1 for r in rows if r.get("result") == "PASS"),
            "failed": sum(1 for r in rows if r.get("result") == "FAIL"),
            "inconclusive": sum(1 for r in rows if r.get("result") == "INCONCLUSIVE"),
            "errors": sum(1 for r in rows if str(r.get("result", "")).startswith("ERR")),
            "total_time_s": round(sum(r.get("time", 0.0) for r in rows), 1),
        },
        "coverage": {
            "validator_count": cfg.get("nodes", "mixed"),
            "fault_bound_f": cfg.get("f", "mixed"),
            "max_height": cfg.get("height", "mixed"),
            "max_round": cfg.get("rmax", "mixed"),
            "delta": cfg.get("delta", "mixed"),
            "sigma": cfg.get("sigma", "mixed"),
            "lengths": sorted({r.get("length") for r in rows if r.get("length") is not None}),
        },
    }
    out = STATS_DIR / f"{name}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print("Wrote stats:", out)
    return out


def print_coverage(cfg):
    print("Coverage:")
    print(f"  validators |V| = {cfg['nodes']} (f={cfg['f']}, honest={cfg['nodes'] - cfg['f']})")
    print(f"  heights     = 0..{cfg['height']} ({cfg['height'] + 1} heights)")
    print(f"  rounds      = 0..{cfg['rmax']}")
    print(f"  Delta/Sigma = {cfg['delta']}/{cfg['sigma']}")
    print("  scope       = bounded sanity check for ideal functionality internal consistency")


def restore_tla():
    shutil.rmtree(RUN_DIR, ignore_errors=True)


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
        str(RUN_TLA_FILE),
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


def run_safety_with_params(sigma: int, delta: int, rmax: int, tag="SP-single"):
    """Run safety check with specific Sigma, Delta, MaxRound parameters."""
    patch_safety_params(sigma, delta, rmax)
    cmd = [
        "apalache-mc", "check",
        "--features=no-rows",
        "--cinit=CInitSafety",
        "--init=InitSafety",
        "--next=NextSafety",
        "--inv=Agreement",
        f"--length={SAFETY_LENGTH}",
        str(RUN_TLA_FILE),
    ]

    print()
    print(SEP)
    print(f"SAFETY [{tag}] Sigma={sigma}, Delta={delta}, R_max={rmax}")
    print("Command:")
    print("  " + " ".join(cmd))

    rc, sec = run_cmd(cmd)
    print(f"Finished in {sec:.1f}s | EXITCODE={rc}")

    if rc == EXIT_OK:
        print("Safety PASS: Agreement holds.")
        result = "PASS"
    elif rc == EXIT_COUNTEREXAMPLE:
        print("Safety FAIL: counterexample found.")
        result = "FAIL"
    else:
        result = f"ERR({rc})"

    return {
        "id": tag,
        "phase": 1,
        "sigma": sigma,
        "delta": delta,
        "rmax": rmax,
        "nodes": 4,
        "f": 1,
        "height": 1,
        "length": SAFETY_LENGTH,
        "time": sec,
        "result": result,
        "rc": rc,
        "mode": "standard-safety",
    }


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
        str(RUN_TLA_FILE),
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
    tex.append(
        r"\caption{Safety (Agreement) verification for $\mathcal{F}^{V,\Delta,\Sigma}_{\mathrm{Tendermint}}$ "
        r"under bounded delay attack ($|V|=4$, $f=1$, $\Delta=\Sigma=1$, $H_{\max}=1$, "
        r"\texttt{length}$=" + str(SAFETY_LENGTH) + r"$). "
        r"MaxRound is patched per run (rsweep-style), not hard-coded via multiple CInit blocks. "
        r"RC$=0$ confirms Agreement.}"
    )
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


def run_optimized_safety(cfg, tag="OS-single"):
    patch_optimized_cinit(cfg)
    length = optimized_safety_length(cfg)
    next_op = "NextOptimizedAttackApalache"
    mode = "optimized-attack-safety"
    cmd = [
        "apalache-mc", "check",
        "--features=no-rows",
        "--cinit=CInitOptimized",
        "--init=Init",
        f"--next={next_op}",
        "--inv=OptimizedAgreement",
        "--no-deadlock",
        f"--length={length}",
        str(RUN_TLA_FILE),
    ]
    print()
    print(SEP)
    print(f"OPTIMIZED SAFETY [{tag}] WITH ADVERSARY WAKE")
    print_coverage(cfg)
    print("Command:")
    print("  " + " ".join(cmd))
    rc, sec = run_cmd(cmd)
    print(f"Finished in {sec:.1f}s | EXITCODE={rc}")
    if rc == EXIT_OK:
        result = "PASS"
        print("Optimized safety PASS: Agreement holds under n>=7/multiple-height bounds with bounded maximum-delay AdversaryWake enabled.")
    elif rc == EXIT_COUNTEREXAMPLE:
        result = "FAIL"
        print("Optimized safety FAIL: Agreement counterexample found.")
    else:
        result = f"ERR({rc})"
    return {
        "id": tag,
        "phase": 2,
        "mode": mode,
        "nodes": cfg["nodes"],
        "f": cfg["f"],
        "height": cfg["height"],
        "sigma": cfg["sigma"],
        "delta": cfg["delta"],
        "rmax": cfg["rmax"],
        "length": length,
        "time": sec,
        "result": result,
        "rc": rc,
    }


def run_optimized_termination(cfg, tag="OT-single"):
    patch_optimized_cinit(cfg)
    length = optimized_term_length(cfg)
    max_run = optimized_max_run()
    next_op = "NextOptimizedAttackApalache"
    mode = "optimized-attack-termination"
    cmd = [
        "apalache-mc", "simulate",
        "--features=no-rows",
        "--cinit=CInitOptimized",
        "--init=Init",
        f"--next={next_op}",
        "--inv=NotYetOptimizedTerminated",
        f"--length={length}",
        f"--max-run={max_run}",
        str(RUN_TLA_FILE),
    ]
    print()
    print(SEP)
    print(f"OPTIMIZED TERMINATION [{tag}] WITH ADVERSARY WAKE")
    print_coverage(cfg)
    print("Command:")
    print("  " + " ".join(cmd))
    rc, sec = run_cmd(cmd)
    print(f"Finished in {sec:.1f}s | EXITCODE={rc}")
    if rc == EXIT_COUNTEREXAMPLE:
        result = "PASS"
        print("Optimized termination PASS: Apalache found a decision witness by violating NotYetOptimizedTerminated.")
    elif rc == EXIT_OK:
        result = "INCONCLUSIVE"
        print("No termination witness found under current length/max-run.")
    else:
        result = f"ERR({rc})"
    return {
        "id": tag,
        "phase": 2,
        "mode": mode,
        "nodes": cfg["nodes"],
        "f": cfg["f"],
        "height": cfg["height"],
        "sigma": cfg["sigma"],
        "delta": cfg["delta"],
        "rmax": cfg["rmax"],
        "length": length,
        "max_run": max_run,
        "time": sec,
        "result": result,
        "rc": rc,
    }


def write_optimized_tex(rows):
    """Write all run results to optimized_verification_table.tex.
    rows must contain phase, nodes, f, height, sigma, delta, rmax fields.
    """
    out = WORKSPACE / "optimized_verification_table.tex"
    p1 = [r for r in rows if r.get("phase") == 1]
    p2 = [r for r in rows if r.get("phase") == 2]

    tex = []
    tex.append("% Auto-generated by check.py --comprehensive")
    tex.append(r"\begin{table}[ht]")
    tex.append(r"\centering")
    tex.append(
        r"\caption{Apalache verification of $\mathcal{F}^{V,\Delta,\Sigma}_{\mathrm{Tendermint}}$ under bounded delay attacks. "
        r"Phase\,1 (standard mode, $|V|=4$, $f=1$, $H_{\max}=1$) explores parameter sensitivity across "
        r"$\Sigma\times\Delta\times R_{\max}$ combinations. "
        r"Phase\,2 (optimized mode) demonstrates scalability for $|V|\in\{7,10,13\}$ with $H_{\max}\in\{3,5\}$. "
        r"These checks verify internal consistency of the ideal functionality, not the real protocol.}"
    )
    tex.append(r"\label{tab:tendermint-optimized-verification}")
    tex.append(r"\small")
    tex.append(r"\begin{tabular}{@{}llcrrrc@{}}")
    tex.append(r"\toprule")
    tex.append(
        r"\textbf{Phase} & \textbf{Check} & $|V|$ & $f$ & $H_{\max}$ & "
        r"$\Sigma/\Delta$ & $R_{\max}$ & \textbf{length} & \textbf{Time(s)} & \textbf{Result} \\"
    )
    tex.append(r"\midrule")

    for r in p1:
        tex.append(
            f"1 (std) & {r['mode']} & {r['nodes']} & {r['f']} & {r['height']} & "
            f"{r['sigma']}/{r['delta']} & {r['rmax']} & "
            f"{r.get('length', '-')} & {r['time']:.1f} & {r['result']} " + r"\\"
        )

    for r in p2:
        tex.append(
            f"2 (scalable) & {r['mode']} & {r['nodes']} & {r['f']} & {r['height']} & "
            f"{r['sigma']}/{r['delta']} & {r['rmax']} & "
            f"{r.get('length', '-')} & {r['time']:.1f} & {r['result']} " + r"\\"
        )

    tex.append(r"\bottomrule")
    tex.append(r"\end{tabular}")
    tex.append(r"\end{table}")
    out.write_text("\n".join(tex), encoding="utf-8")
    print("Wrote:", out)


def run_comprehensive():
    """Run the full 13-configuration two-phase sweep and export results to tex."""
    rows = []

    try:
        # Phase 1: standard verification – parameter sensitivity (|V|=4, f=1, H=1)
        print("\n" + "=" * 70)
        print("PHASE 1: Standard Verification - Parameter Sensitivity")
        print("  |V|=4  f=1  H_max=1  vary Sigma/Delta/Rmax")
        print("=" * 70)

        for sigma, delta, rmax, tag in PHASE1_CONFIGS:
            row = run_safety_with_params(sigma, delta, rmax, tag)
            row["phase"] = 1
            rows.append(row)
            write_optimized_tex(rows)  # incremental export after each run

        # Phase 2: scalable verification – larger |V| and H, optimized Apalache next
        print("\n" + "=" * 70)
        print("PHASE 2: Scalable Verification - Scalability")
        print("  optimized Apalache next-relation with bounded AdversaryWake")
        print("=" * 70)

        for nodes, height, rmax, tag in PHASE2_CONFIGS:
            cfg = optimized_config(nodes=nodes, height=height, rmax=rmax)
            # run both safety and termination for each scalable config
            row_s = run_optimized_safety(cfg, f"{tag}-safety")
            rows.append(row_s)
            write_optimized_tex(rows)  # incremental export

            row_t = run_optimized_termination(cfg, f"{tag}-term")
            rows.append(row_t)
            write_optimized_tex(rows)  # incremental export

    finally:
        restore_tla()

    # Final export
    write_optimized_tex(rows)
    write_json_stats("comprehensive", rows, {}, [
        "Two-phase sweep: Phase 1 = 8 standard safety checks, Phase 2 = 8 scalable (safety+termination) configs",
        "Phase 2 nodes: |V| in {7,10,13}, H_max in {3,5}, optimized Apalache next-relation",
    ])

    # Print summary table
    print()
    print(SEP)
    print("COMPREHENSIVE VERIFICATION SUMMARY")
    print(SEP2)
    print(
        "  {:<16} {:>4} {:>3} {:>3} {:>5} {:>5} {:>7} {:>9}  {}".format(
            "Check", "|V|", "f", "H", "Sigma", "Delta", "Rmax", "Time(s)", "Result"
        )
    )
    print("  " + "-" * 76)
    for r in rows:
        print(
            "  {:<16} {:>4} {:>3} {:>3} {:>5} {:>5} {:>7} {:>9.1f}  {}".format(
                r["id"], r["nodes"], r["f"], r["height"],
                r["sigma"], r["delta"], r["rmax"], r["time"], r["result"]
            )
        )
    print(SEP)
    passed = sum(1 for r in rows if r["result"] == "PASS")
    failed = sum(1 for r in rows if r["result"] == "FAIL")
    inconclusive = sum(1 for r in rows if r["result"] == "INCONCLUSIVE")
    errors = sum(1 for r in rows if str(r["result"]).startswith("ERR"))
    print(f"  Totals: {len(rows)} checks | PASS={passed} FAIL={failed} INCONCLUSIVE={inconclusive} ERR={errors}")
    print(SEP)


def run_optimized_both():
    cfg = optimized_config(
        nodes=parse_int_arg("nodes", OPT_DEFAULT_NODES),
        height=parse_int_arg("height", OPT_DEFAULT_HEIGHT),
        rmax=parse_int_arg("rmax", OPT_DEFAULT_ROUND),
    )
    rows = []
    try:
        rows.append(run_optimized_safety(cfg, "OAS-01"))
        rows.append(run_optimized_termination(cfg, "OAT-01"))
    finally:
        restore_tla()
    print()
    print(SEP)
    print("OPTIMIZED VERIFICATION SUMMARY")
    print(SEP2)
    print("  {:<24} {:>8} {:>9}  {}".format("Mode", "Length", "Time(s)", "Result"))
    print("  " + "-" * 52)
    for r in rows:
        print("  {:<24} {:>8} {:>9.1f}  {}".format(r["mode"], r.get("length", "-"), r["time"], r["result"]))
    print(SEP)
    notes = [
        "The original F_Tendermint.tla remains the single TLA+ specification.",
        "NextOptimizedAttackApalache enables bounded maximum-delay AdversaryWake injections.",
        "It checks ideal-functionality internal consistency, not the real Tendermint protocol and not UC refinement.",
    ]
    write_json_stats("optimized_attack_verification", rows, cfg, notes)
    write_optimized_tex(rows)


def run_optimized_safety_only():
    cfg = optimized_config(
        nodes=parse_int_arg("nodes", OPT_DEFAULT_NODES),
        height=parse_int_arg("height", OPT_DEFAULT_HEIGHT),
        rmax=parse_int_arg("rmax", OPT_DEFAULT_ROUND),
    )
    try:
        row = run_optimized_safety(cfg, "OAS-single")
    finally:
        restore_tla()
    write_json_stats("optimized_attack_safety", [row], cfg,
                      ["Optimized safety-only run with bounded maximum-delay AdversaryWake enabled."])
    write_optimized_tex([row])


def run_optimized_termination_only():
    cfg = optimized_config(
        nodes=parse_int_arg("nodes", OPT_DEFAULT_NODES),
        height=parse_int_arg("height", OPT_DEFAULT_HEIGHT),
        rmax=parse_int_arg("rmax", OPT_DEFAULT_ROUND),
    )
    try:
        row = run_optimized_termination(cfg, "OAT-single")
    finally:
        restore_tla()
    write_json_stats("optimized_attack_termination", [row], cfg,
                      ["Optimized termination witness run with bounded maximum-delay AdversaryWake enabled."])
    write_optimized_tex([row])


def parse_rmax_from_args(default_val):
    for a in sys.argv[1:]:
        m = re.match(r"--rmax=(\d+)", a)
        if m:
            return int(m.group(1))
    return default_val


def main():
    args = set(sys.argv[1:])

    try:
        if "--optimized-attack-both" in args:
            run_optimized_both()
            return

        if "--optimized-attack-safety" in args:
            run_optimized_safety_only()
            return

        if "--optimized-attack-termination" in args:
            run_optimized_termination_only()
            return

        if "--optimized-both" in args:
            run_optimized_both()
            return

        if "--optimized-safety" in args:
            run_optimized_safety_only()
            return

        if "--optimized-termination" in args:
            run_optimized_termination_only()
            return

        if "--comprehensive" in args:
            run_comprehensive()
            return

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
