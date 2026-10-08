# MarkovProcess consumer pilot

The smallest Lake project that depends on Scott Armstrong's
[MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess) Lean library and proves a
theorem the lab needs, compiled for real. Approved by the Chair (Le Chen) on 2026-10-05.
Design comes from a private study of Armstrong's Lean portfolio (2026-10-05),
section 5.

Status: **builds green, no `sorry`, axioms in {propext, Classical.choice, Quot.sound}.**
Both targets closed: (a) the bridge to Mathlib's Brownian motion and (b) optional stopping at
the truncated exit time of an interval.

## Dependencies and pins

| Item | Pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.35.0-rc2` (prerelease, inherited from MarkovProcess) |
| MarkovProcess | `https://github.com/scottnarmstrong/MarkovProcess.git` @ `666cda029098a1106914fc9fa7abd1727573284a` |
| Mathlib (transitive, via MarkovProcess's `v4.35.0-rc2` tag) | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| batteries / aesop / Qq / proofwidgets / plausible / LeanSearchClient / importGraph / Cli | transitive, see `lake-manifest.json` |

There is a single `require` (MarkovProcess). Lake did not ask for a second Mathlib
requirement. The project uses the Lean module system (`module`, `public import`,
`@[expose] public section`), as MarkovProcess's own files do.

## What it proves

All in `MarkovProcessPilot/BrownianExit.lean`, namespace `MarkovProcessPilot`.

### Part (a): the bridge to Mathlib's Brownian motion

```lean
theorem hasIndepIncrements_iff {T Ω E : Type*} [Preorder T] [MeasurableSpace Ω]
    [MeasurableSpace E] [Sub E] (X : T → Ω → E) (P : Measure Ω) :
    MarkovProcess.HasIndepIncrements X P ↔ ProbabilityTheory.HasIndepIncrements X P :=
  Iff.rfl

theorem isBrownianReal_iff {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) :
    MarkovProcess.IsBrownianReal X P ↔ ProbabilityTheory.IsBrownianReal X P

theorem isBrownianReal_brownianMotion (x : ℝ) :
    ProbabilityTheory.IsBrownianReal
      (fun (t : ℝ≥0) (ω : MarkovProcess.ContinuousPath ℝ) ↦ ω t - x)
      (MarkovProcess.brownianMotion x)

-- a first use of Mathlib's Brownian API through the bridge
theorem integral_eval_brownianMotion (x : ℝ) (t : ℝ≥0) :
    ∫ ω, ω t ∂(MarkovProcess.brownianMotion x) = x
```

The bridge is an exact `Iff` for every process and measure, not only for the canonical one.
`MarkovProcess.HasIndepIncrements` is definitionally Mathlib's (`Iff.rfl` closes it).
The forward direction of `isBrownianReal_iff` is Mathlib's
`HasIndepIncrements.isPreBrownianReal_of_hasLaw`. The reverse direction uses Mathlib's
`IsPreBrownianReal.hasLaw_eval` and `IsPreBrownianReal.hasIndepIncrements`.

Note: the docstring of `MarkovProcess/Examples/BrownianMotion.lean` says Mathlib's
`HasIndepIncrements` and `IsBrownianReal` are "not available at the pinned revision". That is
**not true at the Mathlib this library actually resolves to** (`065356127b1d`): both exist,
and this file compiles against them.

### Part (b): optional stopping at a truncated exit time

```lean
theorem integral_eval_exitTimeTrunc_Ioo (a b x : ℝ) (hax : a < x) (hxb : x < b) (K : ℝ≥0) :
    ∫ ω, ω (MarkovProcess.ContinuousPath.exitTimeTrunc (Set.Ioo a b) K ω)
      ∂(MarkovProcess.brownianMotion x) = x
```

This is exactly the target statement of the study (section 5), with no extra hypothesis. In
words: Brownian motion started at `x ∈ (a, b)` and stopped at its exit time from `(a, b)`,
truncated at any deterministic horizon `K`, has mean `x`.

The study suggested building a clamped stopped martingale and calling
`integral_stoppedValue_eq_of_locallyBounded`. That route is circular, because showing the
stopped process is a martingale is itself optional stopping. The library offers a better
route: **Dynkin's formula at a bounded stopping time**, which it has already derived from
optional stopping.

1. `cutId y = y * φ(y)`, where `φ` is a Mathlib `ContDiffBump` equal to 1 on `[a-1, b+1]`.
   `cutId` is smooth and compactly supported, so it and its second derivative are `C₀`
   functions.
2. `MarkovProcess.mem_generatorDomain_heatSemigroup` and `generator_heatSemigroup` put
   `cutId` in the generator domain, with generator `cutId'' / 2`. That is 0 on `(a-1, b+1)`.
3. `IsFellerKernelSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator`
   is applied with the heat semigroup's `isConservative_heatSemigroup` and
   `kolmogorovRegular_heatSemigroup`, at the stopping time `exitTimeTrunc (Ioo a b) K`
   (`isStoppingTime_exitTimeTrunc`, `exitTimeTrunc_le`). It gives
   `E_x cutId(ω_T) - cutId x = E_x ∫_0^T (cutId''/2)(ω_s) ds`. The inner integral vanishes,
   because `ω_s ∈ (a, b)` for `s < T`.
4. Almost surely `ω 0 = x`, because `brownianMotion_map_eval 0 x` gives
   `gaussianReal x 0 = dirac x`. Then `ω_T ∈ [a, b]` by continuity of the path, where
   `cutId = id`. So `E_x ω_T = cutId x = x`.

Helper results, all proved: `contDiff_cutId`, `hasCompactSupport_cutId`, `cutId_eq_self`,
`iteratedDeriv_two_cutId_eq_zero`, `mem_of_lt_exitTimeTrunc`, `eval_exitTimeTrunc_mem_Icc`
and `ae_eval_zero_eq`. `mem_of_lt_exitTimeTrunc` is adapted, specialised to `ℝ` and made public, from Scott
Armstrong's `private` lemma in `MarkovProcess/Trajectory/DynkinStopping.lean`.

## Axioms

`lake env lean scripts/Axioms.lean` (full output in `logs/axioms.txt`):

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
`sorry|admit|axiom |native_decide` finds nothing.

## How to build

```bash
lake update                 # once; also runs Mathlib's cache fetch via the post-update hook
lake exe cache get          # Mathlib oleans (no-op if already fetched)
lake build                  # builds the needed MarkovProcess modules from source, then the pilot
lake env lean scripts/Axioms.lean
```

MarkovProcess ships no olean cache, so its modules compile from source on first build.

## Build cost (measured on a lab laptop, 2026-10-05)

Host: a lab laptop, Intel i5-11500H (12 threads), 38 GB RAM. The build was pinned to 4
cores with `taskset -c 0-3 nice -n 10` because another Lean build was running on the same host.
`lake build` at this toolchain has no `-j` flag (`error: unknown short option '-j'`), so
`taskset` was used to cap the cores. Times and memory come from `/usr/bin/time -v`. Peak RSS
is the largest single process (getrusage), not the sum across workers.

| Step | Wall time | Peak RSS |
|---|---|---|
| `lake update` (clones 10 packages + Mathlib cache fetch of 8,915 files) | 1:50.6 | 0.95 GB |
| `lake exe cache get` (second call, already cached) | 0:05.9 | 0.80 GB |
| `lake build MarkovProcess` (all 250 MarkovProcess modules from source; 3,514 jobs; 0 warnings) | **3:32.8** (524.7 s user, 351% CPU) | **1.54 GB** |
| `lake build` of the pilot after `rm -rf .lake/build` (MarkovProcess already built) | **0:07.4** (`BrownianExit` 3.2 s) | 1.54 GB |
| `lake env lean scripts/Axioms.lean` | 0:10.6 | n/a |

The study expected "tens of minutes" for MarkovProcess. The real cost is about 3.5 minutes on
4 cores. Logs are in `logs/`.

## What MarkovProcess gave us for free vs what we had to write

**For free (used directly, unmodified):**
- The canonical Brownian motion `brownianMotion : Kernel ℝ (ContinuousPath ℝ)`, its
  identification `isBrownianReal_brownianMotion`, and the one-point law
  `brownianMotion_map_eval`.
- The exit-time API: `exitTimeTrunc`, `isStoppingTime_exitTimeTrunc`, `exitTimeTrunc_le`,
  `coe_exitTimeTrunc`, `mem_of_lt_exitTime`.
- The heat generator: `mem_generatorDomain_heatSemigroup` and `generator_heatSemigroup`, so
  `C²` `C₀` functions with `C₀` second derivative are in the domain, with `L = ½ d²`.
- Feller and Kolmogorov regularity of the heat semigroup: `isFellerKernelSemigroup_heatSemigroup`,
  `isConservative_heatSemigroup` and `kolmogorovRegular_heatSemigroup`.
- **Dynkin's formula at a bounded stopping time**
  (`integral_eval_stoppingTime_sub_eq_integral_integral_generator`). Underneath it sit
  continuous-time optional stopping (`integral_stoppedValue_eq_of_locallyBounded`) and the
  martingale property of the Dynkin process. This was the expensive part, and none of it had
  to be written.

**What we wrote (about 250 lines including docs):**
- The two-way bridge `isBrownianReal_iff` (about 15 lines). The heavy direction is Mathlib's
  `isPreBrownianReal_of_hasLaw`.
- A test function: the identity cut off by a `ContDiffBump`, its `C₀` packaging, and the fact
  that its second derivative vanishes near `[a, b]`.
- The pathwise facts: before `T` the path is in `(a, b)`, and at `T` it is in `[a, b]`.
- `ω 0 = x` almost surely, from the dirac law at time 0.
- The final assembly: the inner integral vanishes almost everywhere, then `integral_congr_ae`.

**Friction points:**
- `Main` does not import `Examples/*`. The pilot imports
  `MarkovProcess.Examples.{BrownianMotion,HeatGenerator}` and
  `MarkovProcess.Trajectory.DynkinStopping` directly.
- The "path is inside `U` before the truncated exit time" lemma is `private` in the library, so
  the pilot had to copy it.
- The library's docstring claim that Mathlib lacks `IsBrownianReal` is stale for its own
  Mathlib pin.

## Not done / out of scope

- Untruncated exit times. The library has `Trajectory/ExpectedExitTime.lean`
  (`ae_exitTime_lt_top`); with dominated convergence it would remove `K` and give the exit
  probability `P_x(exit at b) = (x - a)/(b - a)`. Not attempted.

## Evidence

`.lean-receipts/` holds a lower-tier receipt (build, placeholder scan, `#print axioms`) and a
comparator receipt for the commit that last changed the source: `lake comparator` checks that
the Mathlib-only statement in `Audit/Exit/Challenge.lean` is exactly what
`Audit/Exit/Solution.lean` proves, and replays the proof in the con-ron, NanoDa and Lean
kernels. The package is listed in the [lean-pkg](https://github.com/lean-pkg/lean-pkg) index.

## Citing

This pilot is a thin layer over Scott Armstrong's MarkovProcess, which did the hard part
(see above). If you use it, please cite MarkovProcess as its
[`CITATION.cff`](https://github.com/scottnarmstrong/MarkovProcess/blob/main/CITATION.cff)
asks.

## License

Apache-2.0, see `LICENSE`. MarkovProcess (Apache-2.0, Scott Armstrong) and Mathlib
(Apache-2.0) are dependencies, not vendored, except one lemma adapted from MarkovProcess
(`mem_of_lt_exitTimeTrunc`; its notice is in `MarkovProcessPilot/BrownianExit.lean`).
