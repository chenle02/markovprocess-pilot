# Reproducing and evidence

[Back to README](../README.md) · [Proof outline](proof-outline.md)

## Dependencies and pins

| Item | Pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.35.0-rc2` (prerelease, inherited from MarkovProcess) |
| MarkovProcess | `https://github.com/scottnarmstrong/MarkovProcess.git` @ [`666cda029098a1106914fc9fa7abd1727573284a`](https://github.com/scottnarmstrong/MarkovProcess/tree/666cda029098a1106914fc9fa7abd1727573284a) |
| Mathlib (transitive, via MarkovProcess's `v4.35.0-rc2` tag) | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| batteries / aesop / Qq / proofwidgets / plausible / LeanSearchClient / importGraph / Cli | transitive, see [`lake-manifest.json`](../lake-manifest.json) |

There is a single `require` (MarkovProcess) in
[`lakefile.toml`](../lakefile.toml); Lake did not ask for a second Mathlib
requirement. The project uses the Lean module system (`module`,
`public import`, `@[expose] public section`), as MarkovProcess's own files do.

## How to build

```bash
lake update                 # once; also runs Mathlib's cache fetch via the post-update hook
lake exe cache get          # Mathlib oleans (no-op if already fetched)
lake build                  # builds the needed MarkovProcess modules from source, then the pilot
lake env lean scripts/Axioms.lean
```

MarkovProcess ships no olean cache, so its modules compile from source on the
first build. To build the comparator audit modules as well, run
`lake build Audit`.

## Build cost (measured on a laptop, 2026-10-05)

Host: an Intel i5-11500H laptop (12 threads), 38 GB RAM. The build was pinned
to 4 cores with `taskset -c 0-3 nice -n 10` because another Lean build was
running on the same host. `lake build` at this toolchain has no `-j` flag
(`error: unknown short option '-j'`), so `taskset` was used to cap the cores.
Times and memory come from `/usr/bin/time -v`. Peak RSS is the largest single
process (getrusage), not the sum across workers.

| Step | Wall time | Peak RSS |
|---|---|---|
| `lake update` (clones 10 packages + Mathlib cache fetch of 8,915 files) | 1:50.6 | 0.95 GB |
| `lake exe cache get` (second call, already cached) | 0:05.9 | 0.80 GB |
| `lake build MarkovProcess` (all 250 MarkovProcess modules from source; 3,514 jobs; 0 warnings) | **3:32.8** (524.7 s user, 351% CPU) | **1.54 GB** |
| `lake build` of the pilot after `rm -rf .lake/build` (MarkovProcess already built) | **0:07.4** (`BrownianExit` 3.2 s) | 1.54 GB |
| `lake env lean scripts/Axioms.lean` | 0:10.6 | n/a |

So MarkovProcess costs about 3.5 minutes on 4 cores, not the tens of minutes
one might expect for 250 modules. Logs are in [`logs/`](../logs/).

## Axioms and placeholders

`lake env lean scripts/Axioms.lean` (full output in
[`logs/axioms.txt`](../logs/axioms.txt)):

```text
'MarkovProcessPilot.hasIndepIncrements_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MarkovProcessPilot.isBrownianReal_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MarkovProcessPilot.isBrownianReal_brownianMotion' depends on axioms: [propext, Classical.choice, Quot.sound]
'MarkovProcessPilot.integral_eval_brownianMotion' depends on axioms: [propext, Classical.choice, Quot.sound]
'MarkovProcessPilot.integral_eval_exitTimeTrunc_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'MarkovProcessPilot.eval_exitTimeTrunc_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'MarkovProcessPilot.ae_eval_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MarkovProcessPilot.iteratedDeriv_two_cutId_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A grep of `MarkovProcessPilot.lean` and `MarkovProcessPilot/` for
`sorry|admit|axiom |native_decide` finds nothing. (The `sorry` in
`Audit/*/Challenge.lean` is intentional: a comparator challenge is a statement
with a placeholder proof, and the matching `Solution.lean` proves it.)

## Receipts

[`.lean-receipts/`](../.lean-receipts/) holds two kinds of receipt for commit
[`05d99d75df82`](https://github.com/chenle02/markovprocess-pilot/tree/05d99d75df8235e79902220f0fe13e07e81867ca),
the commit that last changed the Lean source:

- **Lower tier** (`05d99d75df82-*-pilot.json` and its `-lower-report.txt`):
  `lake build`, `lake build Audit`, a placeholder scan and `#print axioms`, at
  Lean `v4.35.0-rc2` and Mathlib `065356127b1d`. Result: 0 `sorry`, axioms
  `propext`, `Classical.choice`, `Quot.sound`.
- **Comparator** (`05d99d75df82-comparator.json` and its two logs):
  `lake comparator`, toolchain mechanism, Lean `v4.35.0-rc2`. For
  [`comparator/config-exit.json`](../comparator/config-exit.json) it checks
  that the Mathlib-only statement `exit_mean` in
  [`Audit/Exit/Challenge.lean`](../Audit/Exit/Challenge.lean) is exactly what
  [`Audit/Exit/Solution.lean`](../Audit/Exit/Solution.lean) proves, with only
  the permitted axioms, and replays the proof in the con-ron, NanoDa and Lean
  kernels. [`comparator/config-smoke.json`](../comparator/config-smoke.json)
  is a smoke test of the same machinery on a trivial statement
  (`two_mul_le`). Both results: `pass`.

The receipts are bound to that commit. Later commits that touch only
documentation, images or repository metadata do not change what was checked;
any change to the Lean source, `lakefile.toml`, `lake-manifest.json` or
`lean-toolchain` would need fresh receipts.

The older `9bb873e7aa31-*` receipts cover the previous source commit, which
differed only in attribution comments in `BrownianExit.lean` (the file header
and one docstring).

## Index listing

The package is listed in the lean-pkg package index at the pin
`05d99d75df82`, with trust level `comparator` and headline
`MarkovProcessPilot.integral_eval_exitTimeTrunc_Ioo`. The index repository may
not be publicly readable; the receipts in this repository are self-contained.
