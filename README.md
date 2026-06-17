# UC-T-BFT Verification Project

Formal verification of the Tendermint ideal functionality
$\mathcal{F}^{V,\Delta,\Sigma}_{\mathrm{Tendermint}}$ under bounded delay attacks,
using TLA+ and the Apalache model checker.

## Verification strategy

The specification is verified in two complementary phases:

| Phase | Mode | Description |
|-------|------|-------------|
| 1 | Standard | Exhaustive bounded model checking of the full interleaved transition
|     relation.  Sweeps $\Sigma\in\{3,4,5\}$ and $\Delta\in\{3,4\}$ to stress-test
|     the delay-attack window on a fixed small validator set. |
| 2 | Scalable | Coalesced honest-transition execution path that updates all honest
|     validators in a single coordinated step, reducing state-space growth from
|     $O(|V|^k)$ to $O(|V|\cdot H_{\max}\cdot R_{\max})$.  Preserves all core protocol
|     semantics and the complete delay-attack surface, enabling verification for
|     $|V|\in\{7,10,13\}$ at $H_{\max}\in\{3,5\}$. |

Both phases check the same logical invariants (`Agreement` for safety, `NotYetTerminated` for liveness) against the single TLA+ specification in `F_Tendermint.tla`.  Phase 2 extends the Phase 1 guarantees to larger validator sets without weakening the properties being verified.

## Environment setup

1. Install Python 3.10+
2. Install Java (required by Apalache)
3. Install [Apalache](https://github.com/informalsystems/apalache) and make `apalache-mc` available in your `PATH`

## Usage

### Phase 1 -- Standard parameter sweep

```bash
python check.py --safety-sweep       # Agreement over R_max = [1,2,3,5,8,10]
python check.py --termination-sweep   # termination witness over R_max = [1,2,3,5,8,10]
python check.py --both               # termination then safety sweep
```

### Phase 2 -- Scalable verification

```bash
# Safety + termination for a single config
python check.py --optimized-both --nodes=7 --height=3 --rmax=2

# Safety only
python check.py --optimized-safety --nodes=10 --height=2 --rmax=3

# Termination witness only
python check.py --optimized-termination --nodes=13 --height=3 --rmax=2
```

### Comprehensive (both phases, 25 configurations)

```bash
python check.py --comprehensive
```

This executes all Phase 1 safety sweeps with aggressive $\Sigma/\Delta$ combinations
and all Phase 2 scalable configurations, then writes `comprehensive_verification_table.tex`.

### Single-run overrides

```bash
python check.py --safety --rmax=3
python check.py --termination --rmax=5
```

### Command-line parameters

| Flag | Description | Default |
|------|-------------|---------|
| `--rmax=N` | MaxRound bound | 2 (safety) / 10 (termination) |
| `--nodes=N` | Validator count (Phase 2) | 7 |
| `--height=N` | MaxHeight (Phase 2) | 2 |
| `--length=N` | Override Phase 2 safety check length | auto |
| `--term-length=N` | Override Phase 2 termination simulation length | auto |
| `--max-run=N` | Override Phase 2 termination simulation runs | 1 |

## Output artifacts

- `_apalache-out/` -- Apalache verification outputs
- `safety_table.tex` -- Phase 1 safety sweep results
- `optimized_verification_table.tex` -- Phase 2 scalable verification results
- `comprehensive_verification_table.tex` -- unified results from `--comprehensive`
- `verification_stats/` -- JSON statistics for each run

## Direct Apalache commands

### Phase 1 -- Safety (bounded check)

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

### Phase 1 -- Termination (simulation)

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

### Phase 2 -- Scalable safety

```bash
apalache-mc check \
  --features=no-rows \
  --cinit=CInitOptimized \
  --init=Init \
  --next=NextOptimizedAttackApalache \
  --inv=OptimizedAgreement \
  --no-deadlock \
  --length=18 \
  F_Tendermint.tla
```

## Notes

- All runs verify internal consistency of the ideal functionality
  $\mathcal{F}^{V,\Delta,\Sigma}_{\mathrm{Tendermint}}$, not the real Tendermint
  protocol and not UC refinement.
- The script creates a temporary copy of `F_Tendermint.tla` for each run;
  the source file is never modified.
- `MaxRound` is patched per run via regex replacement inside the temporary copy.
