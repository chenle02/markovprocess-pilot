# Repository contract

Rules for people and coding agents changing this repository.

## What this repository is

A small Lean 4 pilot built on Scott Armstrong's
[MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess). It is not a
general library. Keep the credit to MarkovProcess at least as prominent as it
is in `README.md`, and keep Armstrong's notice in
`MarkovProcessPilot/BrownianExit.lean`.

## Authority order

1. The Lean source (`MarkovProcessPilot/`, `Audit/`) at commit
   `1548828e63c86f2c3f360ac46ab91ec78ba45276`, and its receipts in
   `.lean-receipts/`.
2. `claims.yaml`.
3. `README.md`, `docs/`, `llms.txt`: presentation; they must agree with 1 and 2.

## Files bound to receipts

The receipts cover the source at `1548828e63c8`. Changing any of these
requires a fresh build, a fresh comparator run and new receipts in the same
pull request:

- `MarkovProcessPilot.lean`, `MarkovProcessPilot/`, `Audit/`, `scripts/*.lean`
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`
- `comparator/`, `claims.yaml`, `verify.sh`

Never edit `.lean-receipts/` or `logs/` by hand.

Documentation, images, `.github/` and other metadata may change without new
receipts.

## Claim boundary

- Headline: `MarkovProcessPilot.integral_eval_exitTimeTrunc_Ioo`, exit time
  **truncated at `K`**. Do not describe it as a result about untruncated exit
  times or exit probabilities.
- Bridge: `MarkovProcessPilot.isBrownianReal_iff`.
- Kernel checking, a green build, comparator acceptance and novelty are
  different claims. The mathematics is classical; do not claim novelty.

## Checks before a pull request

```bash
lake build && lake build Audit
lake env lean scripts/Axioms.lean    # expect propext, Classical.choice, Quot.sound only
grep -rnE 'sorry|admit|axiom |native_decide' MarkovProcessPilot.lean MarkovProcessPilot/   # expect nothing
git diff --check
```

`sorry` in `Audit/*/Challenge.lean` is intentional: those files are
comparator challenges.
