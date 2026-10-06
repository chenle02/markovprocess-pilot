import Mathlib
import MarkovProcessPilot.BrownianExit
import MarkovProcess.Path.RandomShiftMeasurability
import MarkovProcess.Parameterized.ContinuousProcessProperties

/-!
# Comparator solution: the mean of Brownian motion stopped at a truncated exit time

Same statement as `Audit/Exit/Challenge.lean`, proved by bridging to the pilot theorem
`MarkovProcessPilot.integral_eval_exitTimeTrunc_Ioo` (stated for the library law
`MarkovProcess.brownianMotion x` and the library's `exitTimeTrunc`).

The bridge has two pieces.

1. `hittingBtwn_eq_exitTimeTrunc`: pathwise, Mathlib's `hittingBtwn` of `Uᶜ` on `[0, K]` is the
   library's truncated exit time `exitTimeTrunc U K` (for every path and every set `U`).
2. `eq_brownianMotion_of_isBrownianReal`: a law on `C(ℝ≥0, ℝ)` whose coordinate process recentred
   at `x` is `IsBrownianReal` is `MarkovProcess.brownianMotion x`.  Both laws have the same
   finite-dimensional distributions (those of Mathlib's Brownian projective family, shifted by
   `x`), so the kernel equal to `P` at `x` and to `brownianMotion` elsewhere has the
   finite-dimensional distributions of the heat semigroup, and the library's uniqueness theorem
   `MarkovProcess.eq_brownianMotion_of_map_finsetEvaluation` identifies it with `brownianMotion`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MarkovProcessPilot.ExitAudit

/-- **Piece 1.** Mathlib's hitting time of `Uᶜ` between `0` and `K` is the library's exit time
from `U` truncated at `K`, path by path. -/
theorem hittingBtwn_eq_exitTimeTrunc (U : Set ℝ) (K : ℝ≥0) (ω : C(ℝ≥0, ℝ)) :
    hittingBtwn (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) Uᶜ 0 K ω =
      MarkovProcess.ContinuousPath.exitTimeTrunc U K ω := by
  set τ := hittingBtwn (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) Uᶜ 0 K ω with hτ
  have hτK : τ ≤ K := hittingBtwn_le ω
  -- The exit time is at least `τ`: a time outside `U` is either in `[0, K]`, hence after `τ`,
  -- or after `K ≥ τ`.
  have hge : (τ : ℝ≥0∞) ≤ MarkovProcess.ContinuousPath.exitTime U ω := by
    apply le_sInf
    rintro s ⟨t, rfl, ht⟩
    rw [ENNReal.coe_le_coe]
    by_cases htK : t ≤ K
    · exact hittingBtwn_le_of_mem zero_le htK ht
    · exact hτK.trans (le_of_not_ge htK)
  have key : (τ : ℝ≥0∞) = min (MarkovProcess.ContinuousPath.exitTime U ω) (K : ℝ≥0∞) := by
    by_cases hex : ∃ j ∈ Icc (0 : ℝ≥0) K, ω j ∈ Uᶜ
    · have hτeq : τ = sInf (Icc (0 : ℝ≥0) K ∩ {i : ℝ≥0 | ω i ∈ Uᶜ}) := by
        rw [hτ]
        simp only [hittingBtwn, hex, ↓reduceIte]
      have hne : (Icc (0 : ℝ≥0) K ∩ {i : ℝ≥0 | ω i ∈ Uᶜ}).Nonempty := by
        obtain ⟨j, hj, hjU⟩ := hex
        exact ⟨j, hj, hjU⟩
      -- The exit time is at most `τ`: it is at most every time of the set whose infimum is `τ`.
      have hle : MarkovProcess.ContinuousPath.exitTime U ω ≤ (τ : ℝ≥0∞) := by
        apply le_of_forall_gt_imp_ge_of_dense
        intro c hc
        rcases eq_or_ne c ⊤ with rfl | hctop
        · exact le_top
        lift c to ℝ≥0 using hctop
        have hc' : sInf (Icc (0 : ℝ≥0) K ∩ {i : ℝ≥0 | ω i ∈ Uᶜ}) < c := by
          rw [← hτeq]
          exact ENNReal.coe_lt_coe.mp hc
        obtain ⟨t, ⟨_, htU⟩, htc⟩ := exists_lt_of_csInf_lt hne hc'
        exact (MarkovProcess.ContinuousPath.exitTime_le_of_notMem U ω t htU).trans
          (ENNReal.coe_le_coe.mpr htc.le)
      rw [min_eq_left (hle.trans (ENNReal.coe_le_coe.mpr hτK))]
      exact le_antisymm hge hle
    · have hτ' : τ = K := by
        rw [hτ]
        simp only [hittingBtwn, hex, ↓reduceIte]
      have hK : (K : ℝ≥0∞) ≤ MarkovProcess.ContinuousPath.exitTime U ω := by
        apply le_sInf
        rintro s ⟨t, rfl, ht⟩
        rw [ENNReal.coe_le_coe]
        by_contra h
        exact hex ⟨t, ⟨zero_le, (not_le.mp h).le⟩, ht⟩
      rw [hτ', min_eq_right hK]
  rw [← WithTop.coe_inj, MarkovProcess.ContinuousPath.coe_exitTimeTrunc]
  exact key

/-- **Piece 2.** A law on path space under which the coordinate process recentred at `x` is a
Brownian motion in Mathlib's sense is the library's Brownian motion started at `x`. -/
theorem eq_brownianMotion_of_isBrownianReal (P : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure P]
    (x : ℝ) (hP : IsBrownianReal (fun t ω ↦ ω t - x) P) :
    P = MarkovProcess.brownianMotion x := by
  have hB := MarkovProcessPilot.isBrownianReal_brownianMotion x
  -- Same finite-dimensional distributions.
  have hmap : ∀ I : Finset ℝ≥0,
      P.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        (MarkovProcess.brownianMotion x).map
          (MarkovProcess.ContinuousPath.finsetEvaluation I) := by
    intro I
    have hrec : Measurable (fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (fun t ↦ ω t - x)) := by
      refine Measurable.of_eval fun t ↦ ?_
      exact (ContinuousMap.measurable_eval (t : ℝ≥0)).sub_const x
    have hshift : Measurable (fun v : I → ℝ ↦ fun t ↦ v t + x) :=
      Measurable.of_eval fun t ↦ (measurable_pi_apply (X := fun _ : I ↦ ℝ) t).add_const x
    have hcomp : MarkovProcess.ContinuousPath.finsetEvaluation I =
        (fun v : I → ℝ ↦ fun t ↦ v t + x) ∘
          (fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (fun t ↦ ω t - x)) := by
      funext ω t
      simp [MarkovProcess.ContinuousPath.finsetEvaluation,
        MarkovProcess.ContinuousPath.finiteEvaluation, Finset.restrict]
    have h1 := (hP.hasLaw I).map_eq
    have h2 := (hB.hasLaw I).map_eq
    rw [hcomp, ← Measure.map_map hshift hrec, ← Measure.map_map hshift hrec]
    exact congrArg (fun μ ↦ μ.map (fun v : I → ℝ ↦ fun t ↦ v t + x)) (h1.trans h2.symm)
  -- The kernel equal to `P` at `x` and to `brownianMotion` elsewhere is `brownianMotion`.
  let Q : ProbabilityTheory.Kernel ℝ (MarkovProcess.ContinuousPath ℝ) :=
    ProbabilityTheory.Kernel.piecewise (measurableSet_singleton x)
      (ProbabilityTheory.Kernel.const ℝ P) MarkovProcess.brownianMotion
  have hQ : Q = MarkovProcess.brownianMotion := by
    refine MarkovProcess.eq_brownianMotion_of_map_finsetEvaluation Q fun I ↦ ?_
    rw [← MarkovProcess.brownianMotion_map_finsetEvaluation I]
    ext y : 1
    rw [ProbabilityTheory.Kernel.map_apply _
        (MarkovProcess.ContinuousPath.measurable_finsetEvaluation I),
      ProbabilityTheory.Kernel.map_apply _
        (MarkovProcess.ContinuousPath.measurable_finsetEvaluation I)]
    simp only [Q, ProbabilityTheory.Kernel.piecewise_apply, ProbabilityTheory.Kernel.const_apply,
      mem_singleton_iff]
    split_ifs with hy
    · subst hy
      exact hmap I
    · rfl
  have hx := congrArg (fun κ : ProbabilityTheory.Kernel ℝ (MarkovProcess.ContinuousPath ℝ) ↦ κ x) hQ
  simpa [Q, ProbabilityTheory.Kernel.piecewise_apply] using hx

end MarkovProcessPilot.ExitAudit

section ExitMean

/- The library declares its own (definitionally equal) Borel instance on
`MarkovProcess.ContinuousPath ℝ = C(ℝ≥0, ℝ)`.  Remove it here so that the statement below
elaborates with Mathlib's `ContinuousMap.measurableSpace`, exactly as in the Challenge. -/
attribute [-instance] MarkovProcess.ContinuousPath.instMeasurableSpace

theorem exit_mean (P : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure P] (a b x : ℝ)
    (hax : a < x) (hxb : x < b) (hP : IsBrownianReal (fun t ω ↦ ω t - x) P) (K : ℝ≥0) :
    Integrable (fun ω : C(ℝ≥0, ℝ) ↦ ω (hittingBtwn (fun t ω ↦ ω t) (Ioo a b)ᶜ 0 K ω)) P ∧
      ∫ ω, ω (hittingBtwn (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) (Ioo a b)ᶜ 0 K ω) ∂P = x := by
  have hfun : (fun ω : C(ℝ≥0, ℝ) ↦ ω (hittingBtwn (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) (Ioo a b)ᶜ 0 K ω))
      = fun ω ↦ ω (MarkovProcess.ContinuousPath.exitTimeTrunc (Ioo a b) K ω) := by
    funext ω
    rw [MarkovProcessPilot.ExitAudit.hittingBtwn_eq_exitTimeTrunc]
  rw [hfun, MarkovProcessPilot.ExitAudit.eq_brownianMotion_of_isBrownianReal P x hP]
  refine ⟨?_, MarkovProcessPilot.integral_eval_exitTimeTrunc_Ioo a b x hax hxb K⟩
  have hmeas : Measurable (fun ω : MarkovProcess.ContinuousPath ℝ ↦
      ω (MarkovProcess.ContinuousPath.exitTimeTrunc (Ioo a b) K ω)) :=
    MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel _
      (MarkovProcess.ContinuousPath.isStoppingTime_exitTimeTrunc (Ioo a b) isOpen_Ioo K)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (max |a| |b|) ?_
  filter_upwards [MarkovProcessPilot.ae_eval_zero_eq x] with ω hω0
  have h0 : ω 0 ∈ Ioo a b := by
    rw [hω0]
    exact ⟨hax, hxb⟩
  have hmem := MarkovProcessPilot.eval_exitTimeTrunc_mem_Icc K ω h0
  rw [Real.norm_eq_abs]
  exact abs_le_max_abs_abs hmem.1 hmem.2

end ExitMean
