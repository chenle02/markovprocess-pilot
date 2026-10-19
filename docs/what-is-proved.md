# What is proved

A page for mathematicians: each result in mathematical language, beside the Lean
statement that was checked, and the boundary of what is **not** claimed.

Lean checks every step of the proofs below. It cannot check that a Lean statement says
what the words on this page say: that comparison is the reader's. For each result, read
the mathematics beside the Lean statement and check that the hypotheses match.

All results build on Scott Armstrong's
[MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess) library (pinned at
`666cda029098`), which supplies the Brownian motion, exit times, optional stopping and
Dynkin's formula. Checked at commit `1548828e63c8` with Lean `v4.35.0-rc2`; axioms
`propext`, `Classical.choice`, `Quot.sound` only.

## 1. Mean of Brownian motion stopped at a truncated exit time

**Status: proved; the Mathlib-only form was also confirmed by the comparator.**

**In words.** Let $a<x<b$ and $K\ge 0$. Let $\mathbb{P}_x$ be the law of Brownian motion
started at $x$ on the path space $C([0,\infty),\mathbb{R})$, and let

```math
\tau_K(\omega)=\inf\{t\in[0,K]:\ \omega(t)\notin(a,b)\}\wedge K
```

be the exit time from $(a,b)$ truncated at the horizon $K$. Then

```math
\int \omega\bigl(\tau_K(\omega)\bigr)\,\mathbb{P}_x(d\omega)=x .
```

**In Lean (library form).** [`MarkovProcessPilot/BrownianExit.lean`](../MarkovProcessPilot/BrownianExit.lean),
with the library's Brownian motion and its truncated exit time:

```lean
theorem MarkovProcessPilot.integral_eval_exitTimeTrunc_Ioo
    (a b x : ℝ) (hax : a < x) (hxb : x < b) (K : ℝ≥0) :
    ∫ ω, ω (MarkovProcess.ContinuousPath.exitTimeTrunc (Set.Ioo a b) K ω)
      ∂(MarkovProcess.brownianMotion x) = x
```

**In Lean (Mathlib-only form, compared).** [`Audit/Exit/Challenge.lean`](../Audit/Exit/Challenge.lean):
for *any* probability measure $P$ on $C(\mathbb{R}_{\ge0},\mathbb{R})$ under which
$t\mapsto\omega(t)-x$ is a real Brownian motion (Mathlib's `IsBrownianReal`), with Mathlib's
`hittingBtwn` as the stopping time, the stopped position is integrable and has mean $x$:

```lean
theorem exit_mean (P : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure P] (a b x : ℝ)
    (hax : a < x) (hxb : x < b) (hP : IsBrownianReal (fun t ω ↦ ω t - x) P) (K : ℝ≥0) :
    Integrable (fun ω : C(ℝ≥0, ℝ) ↦ ω (hittingBtwn (fun t ω ↦ ω t) (Ioo a b)ᶜ 0 K ω)) P ∧
      ∫ ω, ω (hittingBtwn (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) (Ioo a b)ᶜ 0 K ω) ∂P = x
```

**Hypotheses.** Exactly those shown: $a<x<b$, a deterministic horizon $K$, and (for the
compared form) that $P$ is a law of Brownian motion started at $x$.

## 2. The library's Brownian motion is Brownian motion in Mathlib's sense

**Status: proved; a stronger Mathlib-only form was confirmed by the comparator.**

**In words.** For every $x\in\mathbb{R}$, under the library's law $\mathbb{P}_x$ the
recentred coordinate process $t\mapsto\omega(t)-x$ is a real Brownian motion in Mathlib's
sense. More generally, the library's notion `MarkovProcess.IsBrownianReal X P` and Mathlib's
`ProbabilityTheory.IsBrownianReal X P` are equivalent for every process $X$ and measure $P$
(`MarkovProcessPilot.isBrownianReal_iff`).

**In Lean.** [`MarkovProcessPilot/BrownianExit.lean`](../MarkovProcessPilot/BrownianExit.lean):

```lean
theorem isBrownianReal_brownianMotion (x : ℝ) :
    ProbabilityTheory.IsBrownianReal
      (fun (t : ℝ≥0) (ω : MarkovProcess.ContinuousPath ℝ) ↦ ω t - x)
      (MarkovProcess.brownianMotion x)
```

**Compared form.** [`Audit/BrownianKernel/Challenge.lean`](../Audit/BrownianKernel/Challenge.lean)
states, in Mathlib's vocabulary only, that there is exactly one Markov kernel
$\kappa:\mathbb{R}\to C(\mathbb{R}_{\ge0},\mathbb{R})$ such that $t\mapsto\omega(t)-x$ is a
real Brownian motion under $\kappa(x)$ for every $x$:

```lean
theorem exists_unique_brownian_kernel :
    ∃! κ : Kernel ℝ C(ℝ≥0, ℝ),
      IsMarkovKernel κ ∧ ∀ x : ℝ, IsBrownianReal (fun t ω ↦ ω t - x) (κ x)
```

A Mathlib-only statement cannot name the library's kernel, so this form is stronger than
the library theorem: its proof uses `MarkovProcess.brownianMotion` as the witness together
with the library's uniqueness theorem.

## Not proved here

- Untruncated exit times: $`\tau=\inf\{t\ge0:\omega(t)\notin(a,b)\}`$ without the horizon $K$.
- The exit probability $\mathbb{P}_x(\text{exit at } b)=(x-a)/(b-a)$.
- Anything about Brownian motion that MarkovProcess or Mathlib does not already provide;
  this is a thin consumer pilot, and the mathematics is classical. No new theorem is claimed.

## How this was checked

- `lake build` with no `sorry`, `admit`, custom `axiom` or `native_decide` in
  `MarkovProcessPilot/`; axioms recorded in [`logs/axioms.txt`](../logs/axioms.txt).
- The comparator checked each Challenge statement above against its `Solution.lean`
  (Lean kernel plus the independent kernels con-ron and NanoDa).
- Receipts: [`.lean-receipts/`](../.lean-receipts/), bound to commit `1548828e63c8`;
  reproduction steps in [reproducing.md](reproducing.md).

This page is written by hand. The page lean-pkg generates from `coverage.yaml` is not yet
available for this package: its recorded comparator receipt includes a toolchain smoke test
that no result names.
