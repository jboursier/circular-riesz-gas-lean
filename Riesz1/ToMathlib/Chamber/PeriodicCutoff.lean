/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Chamber.PeriodizationIntegral
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A smooth partition under integer translations

The difference of two translated smooth step functions has support in
`[-1, 1]`. Its integer translates sum exactly to one. It localizes a
periodic function on the cover while preserving it after periodization.
-/

@[expose] public section

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The smooth compact cutoff whose integer translates form a partition of one. -/
def periodicCutoff (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t

theorem contDiff_periodicCutoff : ContDiff ℝ ∞ periodicCutoff :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem periodicCutoff_eq_zero {t : ℝ} (ht : t ≤ -1 ∨ 1 ≤ t) : periodicCutoff t = 0 := by
  rcases ht with ht | ht
  · rw [periodicCutoff, Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]
  · rw [periodicCutoff, Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le ht, sub_self]

theorem hasCompactSupport_periodicCutoff : HasCompactSupport periodicCutoff := by
  apply (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).of_isClosed_subset
    (isClosed_tsupport periodicCutoff)
  apply closure_minimal _ isClosed_Icc
  intro t ht
  constructor <;> by_contra h
  · exact ht (periodicCutoff_eq_zero (Or.inl (le_of_lt (lt_of_not_ge h))))
  · exact ht (periodicCutoff_eq_zero (Or.inr (le_of_lt (lt_of_not_ge h))))

/-- The locally finite sum of all integer translates is exactly one. -/
theorem finsum_periodicCutoff (t : ℝ) : ∑ᶠ k : ℤ, periodicCutoff (t + k) = 1 := by
  classical
  let m := ⌊t⌋
  let s : Finset ℤ := {-m - 1, -m}
  have h0 : (0 : ℝ) ≤ t - m := sub_nonneg.mpr (Int.floor_le t)
  have h1 : t - m < (1 : ℝ) := by
    have hh := Int.lt_floor_add_one t
    change t - (⌊t⌋ : ℝ) < 1
    linarith
  rw [finsum_eq_sum_of_support_subset _ (s := s) (by
    intro k hk
    by_contra hks
    have hne₁ : k ≠ -m - 1 := by simpa [s] using (not_or.mp (by simpa [s] using hks)).1
    have hne₂ : k ≠ -m := by simpa [s] using (not_or.mp (by simpa [s] using hks)).2
    have hk' : k ≤ -m - 2 ∨ -m + 1 ≤ k := by omega
    apply hk
    apply periodicCutoff_eq_zero
    rcases hk' with hk' | hk'
    · left
      have : (k : ℝ) ≤ -m - 2 := by exact_mod_cast hk'
      linarith
    · right
      have : -(m : ℝ) + 1 ≤ k := by exact_mod_cast hk'
      linarith)]
  have hne : -m - 1 ≠ -m := by omega
  have hmem : -m - 1 ∉ ({-m} : Finset ℤ) := by simpa only [Finset.mem_singleton] using hne
  simp only [s, Finset.sum_insert hmem, Finset.sum_singleton,
    periodicCutoff, Int.cast_sub, Int.cast_neg, Int.cast_one]
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : t + (-↑m - 1) ≤ 0),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t + -↑m + 1)]
  rw [show t + (-↑m - 1) + 1 = t + -↑m by ring]
  ring

/-- A smooth strip cutoff reconstructs a periodic function by periodization. -/
theorem vectorPeriodize_periodicCutoff_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : E} (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1)
    {b : E → ℝ} (hb : ∀ (k : ℤ) x, b (x + (k : ℝ) • v) = b x)
    (hs : HasCompactSupport (fun x => periodicCutoff (ℓ x) * b x)) :
    vectorPeriodize v hv (fun x => periodicCutoff (ℓ x) * b x) hs = b := by
  funext x
  simp only [vectorPeriodize, map_add, map_smul, hℓ, smul_eq_mul, mul_one, hb]
  rw [← finsum_mul, finsum_periodicCutoff, one_mul]

end Riesz1

end
