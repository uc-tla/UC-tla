# UC-T-BFT Verification Project

Minimal project for model checking `F_Tendermint.tla` with Apalache.

## Main runner

- `check.py`

## Environment setup

1. Install Python 3.10+.
2. Install Java (required by Apalache).
3. Install Apalache and make `apalache-mc` available in your `PATH`.

A common way is to download the release package from the Apalache GitHub releases page,
then run `apalache-mc` directly (or add its `bin` directory to `PATH`).

## Script-based usage (`check.py`)

Run from project root:

```bash
python check.py --termination
python check.py --safety
python check.py --termination-sweep
python check.py --safety-sweep
python check.py --both
```

### Parameters and defaults

- `--termination`
  - single termination run
  - default: `--rmax=10`
- `--safety`
  - single safety run
  - default: `--rmax=2`
- `--termination-sweep`
  - termination sweep over `R = [1, 2, 3, 5, 8, 10]`
- `--safety-sweep`
  - safety sweep over `R = [1, 2, 3, 5, 8, 10]`
  - also writes `safety_table.tex`
- `--both`
  - runs termination sweep then safety sweep
- `--rmax=N`
  - only used by single-run modes (`--termination` or `--safety`)
  - note: use `--rmax=5` format (with `=`)

Examples:

```bash
python check.py --termination --rmax=5
python check.py --safety --rmax=3
```

## Direct Apalache commands (without script)

If you do not use `check.py`, run Apalache directly as below.

### Termination (simulate)

```bash
apalache-mc simulate \
  --features=no-rows \
  --cinit=CInit \
  --init=Init \
  --next=NextBoundedAttack \
  --inv=NotYetTerminated \
  --length=100 \
  --max-run=60 \
  F_Tendermint.tla
```

### Safety (check)

```bash
apalache-mc check \
  --features=no-rows \
  --cinit=CInitSafety \
  --init=InitSafety \
  --next=NextSafety \
  --inv=Agreement \
  --length=5 \
  F_Tendermint.tla
```

### Note on `R_max`

`R_max` is controlled by the constant `MaxRound` in `CInit` / `CInitSafety`.
The script patches this value automatically for each run.
If you run Apalache directly, edit `MaxRound` in `F_Tendermint.tla` manually before running.

## Output

- Verification outputs are written under `_apalache-out/`.
