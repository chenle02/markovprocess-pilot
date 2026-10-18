import Mathlib
import MarkovProcessPilot.BrownianExit
import MarkovProcess.Path.RandomShiftMeasurability
import MarkovProcess.Parameterized.ContinuousProcessProperties

/-!
# Comparator solution: the Brownian kernel on path space

Same statement as `Audit/BrownianKernel/Challenge.lean`.

* Existence: the witness is the library kernel `MarkovProcess.brownianMotion`, a
  Markov kernel (`MarkovProcess.isMarkovKernel_brownianMotion`), and the pilot
  theorem `MarkovProcessPilot.isBrownianReal_brownianMotion` is exactly the
  second conjunct at each `x`.
* Uniqueness: at each `x`, a probability measure under which the recentred
  coordinate process is `IsBrownianReal` is `MarkovProcess.brownianMotion x`
  (`MarkovProcessPilot.BrownianKernelAudit.eq_brownianMotion_of_isBrownianReal`,
  the same bridge as piece 2 of `Audit/Exit/Solution.lean`, repeated here because
  a Solution module cannot import another configuration's Solution), so two
  Brownian kernels agree at every point.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MarkovProcessPilot.BrownianKernelAudit

/-- A law on path space under which the coordinate process recentred at `x` is a
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

end MarkovProcessPilot.BrownianKernelAudit

section BrownianKernel

/- As in `Audit/Exit/Solution.lean`: remove the library's (definitionally equal)
Borel instance on `MarkovProcess.ContinuousPath ℝ = C(ℝ≥0, ℝ)`, so that the
statement elaborates with Mathlib's `ContinuousMap.measurableSpace`. -/
attribute [-instance] MarkovProcess.ContinuousPath.instMeasurableSpace

theorem exists_unique_brownian_kernel :
    ∃! κ : Kernel ℝ C(ℝ≥0, ℝ),
      IsMarkovKernel κ ∧ ∀ x : ℝ, IsBrownianReal (fun t ω ↦ ω t - x) (κ x) := by
  refine ⟨MarkovProcess.brownianMotion,
    ⟨MarkovProcess.isMarkovKernel_brownianMotion,
      MarkovProcessPilot.isBrownianReal_brownianMotion⟩, ?_⟩
  rintro κ ⟨hκ, hB⟩
  ext1 x
  exact MarkovProcessPilot.BrownianKernelAudit.eq_brownianMotion_of_isBrownianReal (κ x) x (hB x)

end BrownianKernel
