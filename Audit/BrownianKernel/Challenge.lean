import Mathlib

/-!
# Comparator challenge: the Brownian kernel on path space

Statement only, in Mathlib's vocabulary and nothing else.

* The path space is `C(ℝ≥0, ℝ)` with Mathlib's Borel sigma-algebra
  (`ContinuousMap.measurableSpace`), as in `Audit/Exit/Challenge.lean`.
* A Brownian kernel is a Markov kernel `κ` from `ℝ` to path space such that, for
  every starting point `x`, the coordinate process recentred at `x`,
  `t ↦ ω t - x`, is a real Brownian motion under `κ x` in Mathlib's sense
  (`ProbabilityTheory.IsBrownianReal`).

Claim: there is exactly one Brownian kernel.

The pilot's theorem `MarkovProcessPilot.isBrownianReal_brownianMotion` says that
the MarkovProcess library's kernel `MarkovProcess.brownianMotion` has this
property. A Mathlib-only statement cannot name that kernel, so the Challenge
states that the property determines a unique kernel; the Solution proves it with
the library's kernel as the witness and the library's uniqueness theorem. The
Challenge is therefore stronger than the pilot theorem, not equal to it: it is
the pilot theorem, plus `IsMarkovKernel MarkovProcess.brownianMotion`, plus
uniqueness, with the library's kernel replaced by the unique kernel it forces.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem exists_unique_brownian_kernel :
    ∃! κ : Kernel ℝ C(ℝ≥0, ℝ),
      IsMarkovKernel κ ∧ ∀ x : ℝ, IsBrownianReal (fun t ω ↦ ω t - x) (κ x) := by
  sorry
