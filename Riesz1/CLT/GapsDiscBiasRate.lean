/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscScale

/-!
# Vanishing of the bias averaging rate

The numerical limit in Corollary 1.
No probability measure or rigidity hypothesis is needed.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Riesz1

lemma gapsDisc_biasWindow_tendsto_atTop {ι : Type*} {l : Filter ι}
    (k : ι → ℕ) (hk : Tendsto k l atTop) :
    Tendsto (fun n => gapBiasWindow (k n)) l atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hk.eventually (eventually_ge_atTop (b * b))] with n hn
  exact Nat.le_sqrt.mpr hn

/-- The second bias term is bounded by a negative power of the block length. -/
lemma gapsDisc_biasWindow_ratio_le (s : RieszExponent) (k : ℕ) (hk : 1 ≤ k) :
    (gapBiasWindow k : ℝ) ^ (3 * s.val / 4) / (k : ℝ) ^ (s.val / 2) ≤
      (k : ℝ) ^ (-s.val / 8) := by
  have hs := s.2.1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (gapBiasWindow k : ℝ) ≤ Real.sqrt (k : ℝ) := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
    exact_mod_cast Nat.sqrt_le' k
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (gapBiasWindow k)) hm
    (show 0 ≤ 3 * s.val / 4 by positivity)
  have heq : Real.sqrt (k : ℝ) ^ (3 * s.val / 4) = (k : ℝ) ^ (3 * s.val / 8) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hk0.le]
    congr 1
    ring
  rw [heq] at hpow
  apply (div_le_div_of_nonneg_right hpow (Real.rpow_nonneg hk0.le _)).trans_eq
  rw [← Real.rpow_sub hk0]
  congr 1
  ring

/-- The complete bound tends to zero, uniformly in every test function. -/
theorem gapsDisc_bias_rate_tendsto_zero (s : RieszExponent) {ι : Type*} {l : Filter ι}
    (k : ι → ℕ) (hk : Tendsto k l atTop) :
    Tendsto (fun n => (gapBiasWindow (k n) : ℝ) ^ (3 * s.val / 4 - 1) +
      (gapBiasWindow (k n) : ℝ) ^ (3 * s.val / 4) / (k n : ℝ) ^ (s.val / 2)) l (𝓝 0) := by
  have hs := s.2.1
  have hkt : Tendsto (fun n => (k n : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hk
  have hmt : Tendsto (fun n => (gapBiasWindow (k n) : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp (gapsDisc_biasWindow_tendsto_atTop k hk)
  have hfirst : Tendsto (fun n => (gapBiasWindow (k n) : ℝ) ^ (3 * s.val / 4 - 1)) l (𝓝 0) := by
    have he : 0 < 1 - 3 * s.val / 4 := by linarith [s.2.2]
    simpa only [Function.comp_def, show -(1 - 3 * s.val / 4) = 3 * s.val / 4 - 1 by ring] using
      (tendsto_rpow_neg_atTop he).comp hmt
  have hlast : Tendsto (fun n => (k n : ℝ) ^ (-s.val / 8)) l (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (show 0 < s.val / 8 by positivity)).comp hkt
  have hsecond : Tendsto (fun n => (gapBiasWindow (k n) : ℝ) ^ (3 * s.val / 4) /
      (k n : ℝ) ^ (s.val / 2)) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hlast
    filter_upwards [hk.eventually (eventually_ge_atTop 1)] with n hn
    exact gapsDisc_biasWindow_ratio_le s (k n) hn
  simpa only [add_zero] using hfirst.add hsecond

end Riesz1

end
end
