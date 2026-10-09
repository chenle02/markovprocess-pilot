## Summary

<!-- What changed and why. -->

## Scope

- [ ] Presentation only (README, `docs/`, images, `.github/`, metadata): no new receipts needed.
- [ ] Touches receipt-bound files (Lean source, `Audit/`, `scripts/*.lean`, `lakefile.toml`,
      `lake-manifest.json`, `lean-toolchain`, `comparator/`, `claims.yaml`): fresh build,
      comparator run and receipts are included.
- [ ] No theorem-boundary change, or the change is stated here and mirrored in `README.md`,
      `docs/`, `claims.yaml` and `llms.txt`.
- [ ] Credit to Scott Armstrong's MarkovProcess is unchanged or more prominent.

## Validation

<!-- Commands run and their results. -->

- [ ] `lake build` and `lake build Audit`
- [ ] `lake env lean scripts/Axioms.lean` shows only `propext`, `Classical.choice`, `Quot.sound`
- [ ] no `sorry`, `admit`, `axiom` or `native_decide` in `MarkovProcessPilot/`
- [ ] `git diff --check`
- [ ] links checked, when documentation changed
