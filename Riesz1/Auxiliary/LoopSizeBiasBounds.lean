/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasWeight
public import Riesz1.ToMathlib.Moments.SizeBiasedLp
public import Riesz1.ToMathlib.Moments.LpBounds

/-!
# Quantitative size-bias comparison for the anchored law

The `L^p` and event comparisons in the size-bias part of Lemma 5.8, with a
uniform bound for the `L²` norm of `w` from the exponential block moment.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- The displayed norm inequality of the size-bias part of Lemma 5.8.
It holds for every real `p > 0` and every measurable real observable. -/
theorem loopSizeBiased_eLpNorm_le (P : Parameters) (n : ℕ) {T : (Fin (n + 1) → ℝ) → ℝ}
    (hT : Measurable T) {p : ℝ} (hp : 0 < p) :
    eLpNorm T (ENNReal.ofReal p) (loopSizeBiasedLaw P n) ≤
      eLpNorm (loopSizeWeight n) 2 (anchoredLaw P (n + 1)) ^ (1 / p) *
        eLpNorm T (ENNReal.ofReal (2 * p)) (anchoredLaw P (n + 1)) :=
  sizeBiased_eLpNorm_le _ (measurable_loopSizeWeight n) hT hp

/-- The event-indicator case of the same comparison. -/
theorem loopSizeBiased_measure_le (P : Parameters) (n : ℕ) {E : Set (Fin (n + 1) → ℝ)}
    (hE : MeasurableSet E) :
    loopSizeBiasedLaw P n E ≤ eLpNorm (loopSizeWeight n) 2 (anchoredLaw P (n + 1)) *
      (anchoredLaw P (n + 1) E) ^ (1 / 2 : ℝ) :=
  sizeBiased_measure_le _ (measurable_loopSizeWeight n) hE

/-- The size weight has uniformly bounded `L²` norm. The bound is chosen even before the
model parameters. Only the Prékopa–Leindler inequality `External.PrekopaLeindler` is used. -/
theorem loopSizeWeight_eLpNorm_two_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters) (n : ℕ),
      eLpNorm (loopSizeWeight n) 2 (anchoredLaw P (n + 1)) ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB, hb⟩ := blockLength_moments 2 (by norm_num)
  refine ⟨B + 1, by linarith, fun hPL P n => ?_⟩
  have hm := (hb hPL P (n + 1).succPNat (by simp) 0 1 one_pos).2
  simp only [boundary_blockLength_one_eq_gap, Real.rpow_two, Nat.cast_one, one_pow, mul_one] at hm
  have he : (∫⁻ y, ENNReal.ofReal (|loopSizeWeight n y| ^ 2) ∂anchoredLaw P (n + 1)) =
      ∫⁻ X : Configuration (n + 1).succPNat, ENNReal.ofReal (gap X 0 ^ 2) ∂gibbsMeasure P _ := by
    have ha : Measurable (fun X : Configuration (n + 1).succPNat =>
        (anchorCoords (n + 1) X.val).2) :=
      measurable_snd.comp (measurable_anchorCoords_config (n + 1))
    simp only [sq_abs]
    rw [← map_snd_gibbsMeasure P (n + 1), lintegral_map
      (((measurable_loopSizeWeight n).pow_const 2).ennreal_ofReal) ha]
    simp only [loopSizeWeight_anchorCoords]
  have hb2 : B ≤ (B + 1) ^ 2 := by nlinarith
  have h := eLpNorm_le_of_lintegral_pow_le (measurable_loopSizeWeight n)
    (m := 2) (by norm_num) (B := B + 1) (by linarith)
    (he.trans_le (hm.trans (ENNReal.ofReal_le_ofReal hb2)))
  simpa only [Nat.cast_ofNat, ENNReal.ofReal_ofNat] using h

end Riesz1

end
