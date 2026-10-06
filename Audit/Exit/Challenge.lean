import Mathlib

/-!
# Comparator challenge: the mean of Brownian motion stopped at a truncated exit time

Statement only, in Mathlib's vocabulary and nothing else.

* The path space is `C(ℝ≥0, ℝ)` with Mathlib's Borel sigma-algebra
  (`ContinuousMap.measurableSpace`, the Borel sigma-algebra of the compact-open topology).
* `P` is any law on path space under which the coordinate process recentred at `x`,
  `t ↦ ω t - x`, is a real Brownian motion in Mathlib's sense
  (`ProbabilityTheory.IsBrownianReal`: the finite-dimensional laws are those of the
  Brownian projective family, and the paths are a.s. continuous).  In other words `P` is the
  law of Brownian motion started at `x`.
* The stopping time is Mathlib's `MeasureTheory.hittingBtwn` of the closed set `(Ioo a b)ᶜ`
  by the coordinate process between times `0` and `K`: the first time in `[0, K]` at which the
  path leaves `(a, b)`, and `K` if it does not leave by time `K`.

Claim: for `a < x < b` and every horizon `K`, the stopped position is integrable and has mean
`x` (optional stopping / gambler's ruin in mean form).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

theorem exit_mean (P : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure P] (a b x : ℝ)
    (hax : a < x) (hxb : x < b) (hP : IsBrownianReal (fun t ω ↦ ω t - x) P) (K : ℝ≥0) :
    Integrable (fun ω : C(ℝ≥0, ℝ) ↦ ω (hittingBtwn (fun t ω ↦ ω t) (Ioo a b)ᶜ 0 K ω)) P ∧
      ∫ ω, ω (hittingBtwn (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) (Ioo a b)ᶜ 0 K ω) ∂P = x := by
  sorry
