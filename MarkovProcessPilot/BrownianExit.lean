/-
Copyright 2026 Le Chen. Released under the Apache 2.0 license (see LICENSE).

`mem_of_lt_exitTimeTrunc` is adapted from Scott Armstrong's MarkovProcess
(`MarkovProcess/Trajectory/DynkinStopping.lean`,
https://github.com/scottnarmstrong/MarkovProcess), Copyright (c) 2026 Scott Armstrong,
released under the Apache 2.0 license. Changes: specialised to `ℝ` and made public.
-/
module

public import MarkovProcess.Examples.BrownianMotion
public import MarkovProcess.Examples.HeatGenerator
public import MarkovProcess.Trajectory.DynkinStopping
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# A consumer pilot for Scott Armstrong's `MarkovProcess` library

Two results about the canonical Brownian motion `MarkovProcess.brownianMotion x`, the law on
`MarkovProcess.ContinuousPath ℝ` of the Feller process of the heat semigroup started at `x`.

* **Bridge (part a).** `MarkovProcess.IsBrownianReal` and Mathlib's
  `ProbabilityTheory.IsBrownianReal` are equivalent predicates (`isBrownianReal_iff`), and
  `MarkovProcess.HasIndepIncrements` is definitionally Mathlib's `HasIndepIncrements`
  (`hasIndepIncrements_iff`).  Hence the recentred canonical process is a Brownian motion in
  Mathlib's sense (`isBrownianReal_brownianMotion`), and Mathlib's Brownian API applies to it
  (example: `integral_eval_brownianMotion`).
* **Optional stopping at a truncated exit time (part b).** For `a < x < b` and every horizon
  `K`, the path stopped at the exit time of `(a, b)` truncated at `K` has mean `x`
  (`integral_eval_exitTimeTrunc_Ioo`).  The proof is Dynkin's formula at a bounded stopping
  time (`IsFellerKernelSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator`)
  applied to a smooth compactly supported function equal to the identity on a neighbourhood of
  `[a, b]`, whose generator `f'' / 2` (`generator_heatSemigroup`) vanishes there.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcessPilot

noncomputable section

/-! ## Part (a): the bridge to Mathlib's Brownian motion -/

/-- `MarkovProcess.HasIndepIncrements` is a verbatim copy of Mathlib's definition: the two are
definitionally equal. -/
theorem hasIndepIncrements_iff {T Ω E : Type*} [Preorder T] [MeasurableSpace Ω]
    [MeasurableSpace E] [Sub E] (X : T → Ω → E) (P : Measure Ω) :
    MarkovProcess.HasIndepIncrements X P ↔ ProbabilityTheory.HasIndepIncrements X P :=
  Iff.rfl

/-- **The bridge.** `MarkovProcess.IsBrownianReal` (Gaussian marginals, independent increments,
a.s. continuous paths) is equivalent to Mathlib's `ProbabilityTheory.IsBrownianReal`
(finite-dimensional laws of the Brownian projective family, a.s. continuous paths). -/
theorem isBrownianReal_iff {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) :
    MarkovProcess.IsBrownianReal X P ↔ ProbabilityTheory.IsBrownianReal X P := by
  constructor
  · intro h
    exact
      { toIsPreBrownianReal :=
          ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw h.hasLaw_eval
            h.hasIndepIncrements
        cont := h.cont }
  · intro h
    exact
      { hasLaw_eval := h.toIsPreBrownianReal.hasLaw_eval
        hasIndepIncrements := h.toIsPreBrownianReal.hasIndepIncrements
        cont := h.cont }

/-- **The canonical process under `MarkovProcess.brownianMotion x`, recentred at `x`, is a
Brownian motion in Mathlib's sense.** -/
theorem isBrownianReal_brownianMotion (x : ℝ) :
    ProbabilityTheory.IsBrownianReal
      (fun (t : ℝ≥0) (ω : MarkovProcess.ContinuousPath ℝ) ↦ ω t - x)
      (MarkovProcess.brownianMotion x) :=
  (isBrownianReal_iff _ _).1 (MarkovProcess.isBrownianReal_brownianMotion x)

/-- A first use of Mathlib's Brownian API through the bridge: Brownian motion started at `x`
has mean `x` at every time. -/
theorem integral_eval_brownianMotion (x : ℝ) (t : ℝ≥0) :
    ∫ ω, ω t ∂(MarkovProcess.brownianMotion x) = x := by
  have h := (isBrownianReal_brownianMotion x).toIsPreBrownianReal
  have h0 : ∫ ω, (ω t - x) ∂(MarkovProcess.brownianMotion x) = 0 := h.integral_eval t
  have hint : Integrable (fun ω : MarkovProcess.ContinuousPath ℝ ↦ ω t - x)
      (MarkovProcess.brownianMotion x) := h.integrable_eval t
  have hint' : Integrable (fun ω : MarkovProcess.ContinuousPath ℝ ↦ ω t)
      (MarkovProcess.brownianMotion x) := by
    exact (hint.add (integrable_const x)).congr
      (ae_of_all _ fun ω ↦ sub_add_cancel (ω t) x)
  rw [integral_sub hint' (integrable_const x)] at h0
  simpa [sub_eq_zero] using h0

/-! ## Part (b): optional stopping at the truncated exit time of an interval -/

/-- A smooth bump on the line, equal to `1` on `[a - 1, b + 1]`. -/
def bump (a b : ℝ) (hab : a < b) : ContDiffBump ((a + b) / 2) where
  rIn := (b - a) / 2 + 1
  rOut := (b - a) / 2 + 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- The identity cut off by `bump`: smooth, compactly supported, and equal to the identity on
`[a - 1, b + 1]`. -/
def cutId (a b : ℝ) (hab : a < b) (y : ℝ) : ℝ :=
  y * bump a b hab y

theorem contDiff_cutId (a b : ℝ) (hab : a < b) : ContDiff ℝ 2 (cutId a b hab) :=
  contDiff_id.mul (bump a b hab).contDiff

theorem hasCompactSupport_cutId (a b : ℝ) (hab : a < b) : HasCompactSupport (cutId a b hab) :=
  (bump a b hab).hasCompactSupport.mul_left

theorem cutId_eq_self (a b : ℝ) (hab : a < b) {y : ℝ} (hy : y ∈ Icc (a - 1) (b + 1)) :
    cutId a b hab y = y := by
  have hball : y ∈ Metric.closedBall ((a + b) / 2) (bump a b hab).rIn := by
    rw [Real.closedBall_eq_Icc]
    simp only [bump]
    constructor <;> linarith [hy.1, hy.2]
  rw [cutId, (bump a b hab).one_of_mem_closedBall hball, mul_one]

/-- On the open interval `(a - 1, b + 1)` the second derivative of `cutId` vanishes. -/
theorem iteratedDeriv_two_cutId_eq_zero (a b : ℝ) (hab : a < b) {y : ℝ}
    (hy : y ∈ Ioo (a - 1) (b + 1)) : iteratedDeriv 2 (cutId a b hab) y = 0 := by
  have hev : cutId a b hab =ᶠ[𝓝 y] fun z ↦ z := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    exact cutId_eq_self a b hab (Ioo_subset_Icc_self hz)
  rw [hev.iteratedDeriv_eq 2, iteratedDeriv_succ, iteratedDeriv_one]
  simp

/-- `cutId` as a `C₀` function. -/
def cutIdC0 (a b : ℝ) (hab : a < b) : C₀(ℝ, ℝ) where
  toFun := cutId a b hab
  continuous_toFun := (contDiff_cutId a b hab).continuous
  zero_at_infty' := (hasCompactSupport_cutId a b hab).is_zero_at_infty

/-- The second derivative of `cutId` as a `C₀` function. -/
def cutIdDeriv2C0 (a b : ℝ) (hab : a < b) : C₀(ℝ, ℝ) where
  toFun := iteratedDeriv 2 (cutId a b hab)
  continuous_toFun := (contDiff_cutId a b hab).continuous_iteratedDeriv 2 (by norm_num)
  zero_at_infty' := by
    have h : iteratedDeriv 2 (cutId a b hab) = deriv (deriv (cutId a b hab)) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [h]
    exact (hasCompactSupport_cutId a b hab).deriv.deriv.is_zero_at_infty

/-- Strictly before the truncated exit time, the path is still inside `U`. Adapted from Scott
Armstrong's private lemma of the same name in `MarkovProcess.Trajectory.DynkinStopping`,
specialised to `ℝ` and made public. -/
theorem mem_of_lt_exitTimeTrunc (U : Set ℝ) (K : ℝ≥0)
    (ω : MarkovProcess.ContinuousPath ℝ) (t : ℝ≥0)
    (ht : t < MarkovProcess.ContinuousPath.exitTimeTrunc U K ω) : ω t ∈ U := by
  have hlt : ((t : ℝ≥0) : ENNReal) <
      ((MarkovProcess.ContinuousPath.exitTimeTrunc U K ω : ℝ≥0) : ENNReal) :=
    ENNReal.coe_lt_coe.mpr ht
  have hle : ((MarkovProcess.ContinuousPath.exitTimeTrunc U K ω : ℝ≥0) : ENNReal) ≤
      MarkovProcess.ContinuousPath.exitTime U ω := by
    have h : ((MarkovProcess.ContinuousPath.exitTimeTrunc U K ω : ℝ≥0) : WithTop ℝ≥0) ≤
        MarkovProcess.ContinuousPath.exitTimeTop U ω := by
      rw [MarkovProcess.ContinuousPath.coe_exitTimeTrunc]
      exact min_le_left _ _
    exact h
  exact MarkovProcess.ContinuousPath.mem_of_lt_exitTime U ω t (hlt.trans_le hle)

/-- A path started inside `(a, b)` is in `[a, b]` at the truncated exit time of `(a, b)`. -/
theorem eval_exitTimeTrunc_mem_Icc {a b : ℝ} (K : ℝ≥0) (ω : MarkovProcess.ContinuousPath ℝ)
    (h0 : ω 0 ∈ Ioo a b) :
    ω (MarkovProcess.ContinuousPath.exitTimeTrunc (Ioo a b) K ω) ∈ Icc a b := by
  set T := MarkovProcess.ContinuousPath.exitTimeTrunc (Ioo a b) K ω with hTdef
  by_cases hT0 : T = 0
  · rw [hT0]
    exact Ioo_subset_Icc_self h0
  · have hclosed : IsClosed {s : ℝ≥0 | ω s ∈ Icc a b} :=
      isClosed_Icc.preimage ω.continuous
    have hsub : Iio T ⊆ {s : ℝ≥0 | ω s ∈ Icc a b} := fun s hs ↦
      Ioo_subset_Icc_self (mem_of_lt_exitTimeTrunc (Ioo a b) K ω s hs)
    have hTmem : T ∈ closure (Iio T) := by
      rw [closure_Iio' ⟨0, pos_iff_ne_zero.mpr hT0⟩]
      exact Set.mem_Iic.mpr le_rfl
    exact hclosed.closure_subset_iff.mpr hsub hTmem

/-- Brownian motion started at `x` starts at `x` almost surely. -/
theorem ae_eval_zero_eq (x : ℝ) :
    ∀ᵐ ω ∂(MarkovProcess.brownianMotion x), ω 0 = x := by
  have hmap := MarkovProcess.brownianMotion_map_eval 0 x
  rw [gaussianReal_zero_var] at hmap
  have hdirac : ∀ᵐ y ∂(Measure.dirac x), y = x := by
    rw [ae_dirac_eq]
    exact rfl
  rw [← hmap] at hdirac
  exact ae_of_ae_map
    (MarkovProcess.ContinuousPath.measurable_coordinateProcess (alpha := ℝ) 0).aemeasurable hdirac

/-- **Optional stopping at the truncated exit time of an interval (gambler's ruin, mean form).**
For `a < x < b` and every horizon `K`, Brownian motion started at `x` and stopped at the exit time
of `(a, b)` truncated at `K` has mean `x`. -/
theorem integral_eval_exitTimeTrunc_Ioo (a b x : ℝ) (hax : a < x) (hxb : x < b) (K : ℝ≥0) :
    ∫ ω, ω (MarkovProcess.ContinuousPath.exitTimeTrunc (Ioo a b) K ω)
      ∂(MarkovProcess.brownianMotion x) = x := by
  have hab : a < b := hax.trans hxb
  set T := MarkovProcess.ContinuousPath.exitTimeTrunc (Ioo a b) K with hTdef
  have hT := MarkovProcess.ContinuousPath.isStoppingTime_exitTimeTrunc (Ioo a b) isOpen_Ioo K
  have hTK := MarkovProcess.ContinuousPath.exitTimeTrunc_le (Ioo a b) K
  set hF := MarkovProcess.isFellerKernelSemigroup_heatSemigroup with hFdef
  let f : hF.c0Semigroup.generatorDomain :=
    ⟨cutIdC0 a b hab, MarkovProcess.mem_generatorDomain_heatSemigroup (cutIdC0 a b hab)
      (cutIdDeriv2C0 a b hab) (contDiff_cutId a b hab) (fun _ ↦ rfl)⟩
  have hgen : hF.c0Semigroup.generator f = (2 : ℝ)⁻¹ • cutIdDeriv2C0 a b hab :=
    MarkovProcess.generator_heatSemigroup (cutIdC0 a b hab) (cutIdDeriv2C0 a b hab)
      (contDiff_cutId a b hab) (fun _ ↦ rfl)
  have hdyn :
      ∫ ω, (cutIdC0 a b hab) (ω (T ω)) ∂(MarkovProcess.brownianMotion x) - cutIdC0 a b hab x =
        ∫ ω, (∫ s in (0 : ℝ)..(T ω : ℝ), (hF.c0Semigroup.generator f) (ω (Real.toNNReal s)))
          ∂(MarkovProcess.brownianMotion x) :=
    hF.integral_eval_stoppingTime_sub_eq_integral_integral_generator
      MarkovProcess.isConservative_heatSemigroup MarkovProcess.kolmogorovRegular_heatSemigroup
      f T hT hTK x
  have hzero : ∀ ω : MarkovProcess.ContinuousPath ℝ,
      (∫ s in (0 : ℝ)..(T ω : ℝ), (hF.c0Semigroup.generator f) (ω (Real.toNNReal s))) = 0 := by
    intro ω
    have hsingleton : ∀ᵐ s : ℝ ∂(volume : Measure ℝ), s ≠ (T ω : ℝ) := by
      rw [ae_iff]
      simpa only [Ne, not_not, Set.ofPred_eq_eq_singleton] using measure_singleton (T ω : ℝ)
    have hae : ∀ᵐ s : ℝ ∂(volume : Measure ℝ), s ∈ Set.uIoc (0 : ℝ) (T ω : ℝ) →
        (hF.c0Semigroup.generator f) (ω (Real.toNNReal s)) = (fun _ ↦ (0 : ℝ)) s := by
      filter_upwards [hsingleton] with s hs hsmem
      rw [Set.uIoc_of_le (T ω).coe_nonneg] at hsmem
      have hlt : Real.toNNReal s < T ω :=
        (Real.toNNReal_lt_iff_lt_coe hsmem.1.le).mpr (lt_of_le_of_ne hsmem.2 hs)
      have hmem := mem_of_lt_exitTimeTrunc (Ioo a b) K ω _ hlt
      have hmem' : ω (Real.toNNReal s) ∈ Ioo (a - 1) (b + 1) :=
        ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      rw [hgen, ZeroAtInftyContinuousMap.smul_apply]
      change (2 : ℝ)⁻¹ • iteratedDeriv 2 (cutId a b hab) (ω (Real.toNNReal s)) = 0
      rw [iteratedDeriv_two_cutId_eq_zero a b hab hmem', smul_zero]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_zero]
  simp only [hzero, integral_zero] at hdyn
  have hx : cutIdC0 a b hab x = x :=
    cutId_eq_self a b hab ⟨by linarith, by linarith⟩
  have hcongr : (fun ω : MarkovProcess.ContinuousPath ℝ ↦ ω (T ω)) =ᵐ[MarkovProcess.brownianMotion x]
      fun ω ↦ cutIdC0 a b hab (ω (T ω)) := by
    filter_upwards [ae_eval_zero_eq x] with ω hω0
    have h0mem : ω 0 ∈ Ioo a b := by
      rw [hω0]
      exact ⟨hax, hxb⟩
    have hmem := eval_exitTimeTrunc_mem_Icc K ω h0mem
    exact (cutId_eq_self a b hab ⟨by linarith [hmem.1], by linarith [hmem.2]⟩).symm
  rw [integral_congr_ae hcongr]
  linarith [hdyn, hx]

end

end MarkovProcessPilot
