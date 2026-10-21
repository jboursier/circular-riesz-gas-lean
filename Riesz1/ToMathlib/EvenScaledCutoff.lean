/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic

/-!
# Even cutoffs with a uniform derivative bound under rescaling

The explicit cutoff is zero on `[-1/2, 1/2]` and one outside `(-1, 1)`.
Rescaling gives a derivative bound `C / ρ` with the same `C` at every
positive radius `ρ`. This is the cutoff needed to split the inverse kernel
in Lemma 5.3.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- A fixed even smooth transition from zero to one across `1/2 ≤ |t| ≤ 1`. -/
noncomputable def evenUnitCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition ((4 * t ^ 2 - 1) / 3)

theorem evenUnitCutoff_contDiff : ContDiff ℝ ∞ evenUnitCutoff :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const).div_const 3)

theorem evenUnitCutoff_nonneg (t : ℝ) : 0 ≤ evenUnitCutoff t :=
  Real.smoothTransition.nonneg _

theorem evenUnitCutoff_le_one (t : ℝ) : evenUnitCutoff t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem evenUnitCutoff_even (t : ℝ) : evenUnitCutoff (-t) = evenUnitCutoff t := by
  simp only [evenUnitCutoff, neg_sq]

theorem evenUnitCutoff_eq_zero {t : ℝ} (ht : |t| ≤ 1 / 2) : evenUnitCutoff t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have ht' := abs_le.mp ht
  nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (t + 1 / 2)]

theorem evenUnitCutoff_eq_one {t : ℝ} (ht : 1 ≤ |t|) : evenUnitCutoff t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hsq : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  linarith

/-- The derivative vanishes strictly inside both plateau regions. -/
theorem deriv_evenUnitCutoff_eq_zero {t : ℝ}
    (ht : |t| < 1 / 2 ∨ 1 < |t|) : deriv evenUnitCutoff t = 0 := by
  rcases ht with ht | ht
  · have hloc : evenUnitCutoff =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [(continuous_abs.tendsto t).eventually (eventually_lt_nhds ht)] with u hu
      exact evenUnitCutoff_eq_zero hu.le
    rw [hloc.deriv_eq]
    exact deriv_const _ _
  · have hloc : evenUnitCutoff =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
      filter_upwards [(continuous_abs.tendsto t).eventually (eventually_gt_nhds ht)] with u hu
      exact evenUnitCutoff_eq_one hu.le
    rw [hloc.deriv_eq]
    exact deriv_const _ _

/-- One derivative bound for the fixed cutoff. -/
theorem evenUnitCutoff_deriv_bound : ∃ C : ℝ, 0 < C ∧ ∀ t, |deriv evenUnitCutoff t| ≤ C := by
  have hc : Continuous (deriv evenUnitCutoff) :=
    evenUnitCutoff_contDiff.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-2 : ℝ) 2) hc.continuousOn
  refine ⟨max B 0 + 1, by positivity, fun t => ?_⟩
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · have h := hB t ht
    rw [Real.norm_eq_abs] at h
    exact h.trans (by linarith [le_max_left B 0])
  · have habs : 1 < |t| := by
      have h := not_and_or.mp ht
      rcases h with h | h
      · rw [not_le] at h
        have := neg_le_abs t
        linarith
      · rw [not_le] at h
        linarith [le_abs_self t]
    rw [deriv_evenUnitCutoff_eq_zero (Or.inr habs), abs_zero]
    positivity

/-- Smooth cutoffs at every radius, with a common derivative constant chosen
before the radius. Derivatives are supported in the closed transition annulus. -/
theorem exists_even_scaled_cutoff :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧
      (∀ t, χ (-t) = χ t) ∧
      (∀ t, |t| ≤ ρ / 2 → χ t = 0) ∧
      (∀ t, ρ ≤ |t| → χ t = 1) ∧
      (∀ t, |deriv χ t| ≤ C / ρ) ∧
      (∀ t, |t| < ρ / 2 ∨ ρ < |t| → deriv χ t = 0) := by
  obtain ⟨C, hC, hbound⟩ := evenUnitCutoff_deriv_bound
  refine ⟨C, hC, fun ρ hρ => ?_⟩
  let χ : ℝ → ℝ := fun t => evenUnitCutoff (t / ρ)
  have hχ (t : ℝ) : deriv χ t = deriv evenUnitCutoff (t / ρ) / ρ := by
    simpa only [Function.comp_def, id_eq, mul_one_div] using
      ((evenUnitCutoff_contDiff.differentiable (by simp) (t / ρ)).hasDerivAt.comp t
        ((hasDerivAt_id t).div_const ρ)).deriv
  refine ⟨χ, evenUnitCutoff_contDiff.comp (contDiff_id.div_const ρ),
    fun t => ⟨evenUnitCutoff_nonneg _, evenUnitCutoff_le_one _⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    dsimp [χ]
    rw [neg_div, evenUnitCutoff_even]
  · intro t ht
    apply evenUnitCutoff_eq_zero
    rw [abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
    linarith
  · intro t ht
    apply evenUnitCutoff_eq_one
    rw [abs_div, abs_of_pos hρ, le_div_iff₀ hρ]
    simpa using ht
  · intro t
    rw [hχ, abs_div, abs_of_pos hρ]
    exact div_le_div_of_nonneg_right (hbound _) hρ.le
  · intro t ht
    rw [hχ, deriv_evenUnitCutoff_eq_zero, zero_div]
    rcases ht with ht | ht
    · left
      rw [abs_div, abs_of_pos hρ, div_lt_iff₀ hρ]
      linarith
    · right
      rw [abs_div, abs_of_pos hρ, lt_div_iff₀ hρ]
      simpa using ht

end Riesz1
