/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# A sufficient localization exponent

The power comparisons in the localization part of
Lemma 5.8.
-/

@[expose] public section

noncomputable section

namespace Riesz1

/-- The exponent `γ_*(s)`. -/
def loopLocalizationExponent (s : ℝ) : ℝ :=
  max (max 4 (4 / s)) ((3 / 2 - s) / (1 - s))

theorem loopLocalizationExponent_ge_four (s : ℝ) :
    4 ≤ loopLocalizationExponent s :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem loopLocalizationExponent_pos (s : ℝ) : 0 < loopLocalizationExponent s :=
  lt_of_lt_of_le (by norm_num) (loopLocalizationExponent_ge_four s)

/-- The far-field truncation exponent is at most one half. -/
theorem loopLocalization_tail_exponent {s γ : ℝ} (hs1 : s < 1)
    (hγ : loopLocalizationExponent s ≤ γ) :
    2 - s - γ * (1 - s) ≤ 1 / 2 := by
  have h := (le_max_right (max 4 (4 / s)) ((3 / 2 - s) / (1 - s))).trans hγ
  have hd : (3 / 2 - s) ≤ γ * (1 - s) :=
    (div_le_iff₀ (by linarith : 0 < 1 - s)).mp h
  linarith

/-- Any rigidity loss at most `s/4` leaves the exterior contribution below
the required square-root scale. -/
theorem loopLocalization_force_exponent {s γ δ : ℝ} (hs : 0 < s)
    (hγ : loopLocalizationExponent s ≤ γ) (hδ : δ ≤ s / 4) :
    1 - γ * (s / 2 - δ) ≤ 1 / 2 := by
  have hγ4 : 4 ≤ γ := (loopLocalizationExponent_ge_four s).trans hγ
  have h := ((le_max_right 4 (4 / s)).trans
    (le_max_left (max 4 (4 / s)) ((3 / 2 - s) / (1 - s)))).trans hγ
  have hmul : 4 ≤ γ * s := (div_le_iff₀ hs).mp h
  nlinarith

/-- The three powers remaining in the localization proof are absorbed for
every `K ≥ 1`, including the bounded-scale range. -/
theorem loopLocalization_error_powers {s γ δ K : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hγ : loopLocalizationExponent s ≤ γ) (hδ : δ ≤ s / 4) (hK : 1 ≤ K) :
    K ^ (2 - s - γ * (1 - s)) + K ^ (1 - γ * (s / 2 - δ)) + K ^ (-10 : ℝ) ≤
      3 * K ^ (1 / 2 : ℝ) := by
  have htail := Real.rpow_le_rpow_of_exponent_le hK (loopLocalization_tail_exponent hs1 hγ)
  have hforce := Real.rpow_le_rpow_of_exponent_le hK
    (loopLocalization_force_exponent hs hγ hδ)
  have hbad := Real.rpow_le_rpow_of_exponent_le hK (show (-10 : ℝ) ≤ 1 / 2 by norm_num)
  linarith

end Riesz1

end
