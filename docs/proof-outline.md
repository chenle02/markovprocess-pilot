# Proof outline

[Back to README](../README.md) · [Reproducing and evidence](reproducing.md)

Everything below is in
[`MarkovProcessPilot/BrownianExit.lean`](../MarkovProcessPilot/BrownianExit.lean),
namespace `MarkovProcessPilot`. Almost all of the mathematics comes from Scott
Armstrong's [MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess)
library; the last section lists exactly what came from the library and what
this pilot had to write.

<p align="center">
  <img src="assets/exit-time.svg" width="640" alt="Diagram: a Brownian path starts at level x between levels a and b and is stopped at time T, the first time it touches b, which comes before the horizon K. Caption: under the law of Brownian motion started at x, the mean of the path at T is x.">
</p>

## Part (a): the bridge to Mathlib's Brownian motion

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

- The bridge is an exact `Iff` for every process and measure, not only for the
  canonical one.
- `MarkovProcess.HasIndepIncrements` is definitionally Mathlib's (`Iff.rfl`
  closes it).
- The forward direction of `isBrownianReal_iff` is Mathlib's
  `HasIndepIncrements.isPreBrownianReal_of_hasLaw`. The reverse direction uses
  Mathlib's `IsPreBrownianReal.hasLaw_eval` and
  `IsPreBrownianReal.hasIndepIncrements`.

A note on the library at its pinned revision: the docstring of
`MarkovProcess/Examples/BrownianMotion.lean` says Mathlib's
`HasIndepIncrements` and `IsBrownianReal` are "not available at the pinned
revision". At the Mathlib commit the library actually resolves to
(`065356127b1d`) both exist, and this file compiles against them. The
docstring is simply older than the Mathlib pin.

## Part (b): optional stopping at a truncated exit time

```lean
theorem integral_eval_exitTimeTrunc_Ioo (a b x : ℝ) (hax : a < x) (hxb : x < b) (K : ℝ≥0) :
    ∫ ω, ω (MarkovProcess.ContinuousPath.exitTimeTrunc (Set.Ioo a b) K ω)
      ∂(MarkovProcess.brownianMotion x) = x
```

There is no hypothesis beyond `a < x < b`. In words: Brownian motion started at
`x ∈ (a, b)` and stopped at its exit time from `(a, b)`, truncated at any
deterministic horizon `K`, has mean `x`.

### Why not a stopped martingale

One natural plan is to build a clamped stopped martingale and call
`integral_stoppedValue_eq_of_locallyBounded`. That route is circular: showing
the stopped process is a martingale is itself optional stopping. The library
offers a better route, **Dynkin's formula at a bounded stopping time**, which
it has already derived from optional stopping.

### The route through Dynkin's formula

1. `cutId y = y * φ(y)`, where `φ` is a Mathlib `ContDiffBump` equal to 1 on
   `[a-1, b+1]`. `cutId` is smooth and compactly supported, so it and its
   second derivative are `C₀` functions.
2. `MarkovProcess.mem_generatorDomain_heatSemigroup` and
   `generator_heatSemigroup` put `cutId` in the generator domain, with
   generator `cutId'' / 2`. That is 0 on `(a-1, b+1)`.
3. `IsFellerKernelSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator`
   is applied with the heat semigroup's `isConservative_heatSemigroup` and
   `kolmogorovRegular_heatSemigroup`, at the stopping time
   `exitTimeTrunc (Ioo a b) K` (`isStoppingTime_exitTimeTrunc`,
   `exitTimeTrunc_le`). It gives
   `E_x cutId(ω_T) - cutId x = E_x ∫_0^T (cutId''/2)(ω_s) ds`. The inner
   integral vanishes, because `ω_s ∈ (a, b)` for `s < T`.
4. Almost surely `ω 0 = x`, because `brownianMotion_map_eval 0 x` gives
   `gaussianReal x 0 = dirac x`. Then `ω_T ∈ [a, b]` by continuity of the
   path, where `cutId = id`. So `E_x ω_T = cutId x = x`.

Helper results, all proved: `contDiff_cutId`, `hasCompactSupport_cutId`,
`cutId_eq_self`, `iteratedDeriv_two_cutId_eq_zero`, `mem_of_lt_exitTimeTrunc`,
`eval_exitTimeTrunc_mem_Icc` and `ae_eval_zero_eq`.
`mem_of_lt_exitTimeTrunc` is adapted, specialised to `ℝ` and made public, from
Scott Armstrong's `private` lemma in
`MarkovProcess/Trajectory/DynkinStopping.lean`; his copyright notice is at the
top of `BrownianExit.lean`.

## The comparator statement (Mathlib vocabulary only)

The headline theorem is also judged by `lake comparator` against a statement
that uses nothing but Mathlib:
[`Audit/Exit/Challenge.lean`](../Audit/Exit/Challenge.lean), theorem
`exit_mean`.

```lean
theorem exit_mean (P : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure P] (a b x : ℝ)
    (hax : a < x) (hxb : x < b) (hP : IsBrownianReal (fun t ω ↦ ω t - x) P) (K : ℝ≥0) :
    Integrable (fun ω : C(ℝ≥0, ℝ) ↦ ω (hittingBtwn (fun t ω ↦ ω t) (Ioo a b)ᶜ 0 K ω)) P ∧
      ∫ ω, ω (hittingBtwn (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) (Ioo a b)ᶜ 0 K ω) ∂P = x
```

It quantifies over any probability law `P` on `C(ℝ≥0, ℝ)` under which the
recentred coordinate process is Brownian in Mathlib's sense, uses Mathlib's
`hittingBtwn` of `(Ioo a b)ᶜ` on `[0, K]` as the stopping time, and also states
integrability. [`Audit/Exit/Solution.lean`](../Audit/Exit/Solution.lean)
proves it from the pilot theorem in two pieces:

1. `hittingBtwn_eq_exitTimeTrunc`: path by path, Mathlib's `hittingBtwn` of
   `Uᶜ` on `[0, K]` is the library's `exitTimeTrunc U K`.
2. `eq_brownianMotion_of_isBrownianReal`: such a law `P` is
   `MarkovProcess.brownianMotion x`, by the library's uniqueness theorem
   `MarkovProcess.eq_brownianMotion_of_map_finsetEvaluation`.

## What MarkovProcess gave us for free, and what we wrote

**From MarkovProcess (used directly, unmodified):**

- The canonical Brownian motion
  `brownianMotion : Kernel ℝ (ContinuousPath ℝ)`, its identification
  `isBrownianReal_brownianMotion`, and the one-point law
  `brownianMotion_map_eval`.
- The exit-time API: `exitTimeTrunc`, `isStoppingTime_exitTimeTrunc`,
  `exitTimeTrunc_le`, `coe_exitTimeTrunc`, `mem_of_lt_exitTime`.
- The heat generator: `mem_generatorDomain_heatSemigroup` and
  `generator_heatSemigroup`, so `C²` `C₀` functions with `C₀` second
  derivative are in the domain, with `L = ½ d²`.
- Feller and Kolmogorov regularity of the heat semigroup:
  `isFellerKernelSemigroup_heatSemigroup`, `isConservative_heatSemigroup` and
  `kolmogorovRegular_heatSemigroup`.
- **Dynkin's formula at a bounded stopping time**
  (`integral_eval_stoppingTime_sub_eq_integral_integral_generator`).
  Underneath it sit continuous-time optional stopping
  (`integral_stoppedValue_eq_of_locallyBounded`) and the martingale property
  of the Dynkin process. This was the expensive part, and none of it had to be
  written.
- For the comparator solution, the uniqueness theorem
  `eq_brownianMotion_of_map_finsetEvaluation`.

**What this pilot wrote (about 250 lines including docs):**

- The two-way bridge `isBrownianReal_iff` (about 15 lines). The heavy
  direction is Mathlib's `isPreBrownianReal_of_hasLaw`.
- A test function: the identity cut off by a `ContDiffBump`, its `C₀`
  packaging, and the fact that its second derivative vanishes near `[a, b]`.
- The pathwise facts: before `T` the path is in `(a, b)`, and at `T` it is in
  `[a, b]`.
- `ω 0 = x` almost surely, from the dirac law at time 0.
- The final assembly: the inner integral vanishes almost everywhere, then
  `integral_congr_ae`.

**Friction points met while consuming the library:**

- `Main` does not import `Examples/*`. The pilot imports
  `MarkovProcess.Examples.{BrownianMotion,HeatGenerator}` and
  `MarkovProcess.Trajectory.DynkinStopping` directly.
- The "path is inside `U` before the truncated exit time" lemma is `private`
  in the library, so the pilot had to copy it (with attribution).
- The library's docstring claim that Mathlib lacks `IsBrownianReal` is stale
  for its own Mathlib pin.

## Out of scope

- **Untruncated exit times.** The library has
  `Trajectory/ExpectedExitTime.lean` (`ae_exitTime_lt_top`); with dominated
  convergence it would remove `K` and give the exit probability
  `P_x(exit at b) = (x - a)/(b - a)`. Not attempted, and not claimed here.
