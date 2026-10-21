/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscDefs
public import Riesz1.Kernel.PeriodicZeta
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform comparison of the gap normalization with a power

The normalization and limit clauses of
Corollary 1. These facts need no rigidity input.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Riesz1

/-- The zeta combination is uniformly comparable to `t^s` on the half-period. -/
theorem gapsDisc_periodicZeta_comparison (s : RieszExponent) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      c * t ^ s.val ≤ periodicZeta s (t : UnitAddCircle) ∧
        periodicZeta s (t : UnitAddCircle) ≤ C * t ^ s.val := by
  obtain ⟨B, hB, t₀, ht₀, hb⟩ := periodicZeta_asymptotic s
  have he : 0 < 2 - s.val := by linarith [s.2.2]
  have hc : ContinuousAt (fun t : ℝ => B * t ^ (2 - s.val)) 0 :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr he.le))
  have hc0 : Tendsto (fun t : ℝ => B * t ^ (2 - s.val)) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow he.ne'] using hc.tendsto
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hc0 (1 / 2) (by norm_num))
  let d := min (δ / 2) (min t₀ (1 / 4))
  have hd0 : 0 < d := lt_min (by positivity) (lt_min ht₀ (by norm_num))
  have hdt : d ≤ t₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hdhalf : d ≤ 1 / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  have hsmall (t : ℝ) (ht : 0 < t) (htd : t ≤ d) :
      (1 / 2) * t ^ s.val ≤ periodicZeta s (t : UnitAddCircle) ∧
        periodicZeta s (t : UnitAddCircle) ≤ (3 / 2) * t ^ s.val := by
    have hnear : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht]
      exact htd.trans_lt ((min_le_left _ _).trans_lt (by linarith))
    have hpow := hd hnear
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hpow
    have hpoweq : t ^ (2 - s.val) * t ^ s.val = t ^ 2 := by
      rw [← Real.rpow_add ht]
      norm_num
    have hmul := mul_le_mul_of_nonneg_right hpow.le (Real.rpow_nonneg ht.le s.val)
    have herr := abs_le.mp (hb t ht (htd.trans hdt))
    rw [mul_assoc B, hpoweq] at hmul
    constructor <;> nlinarith
  let q := fun t : ℝ => periodicZeta s (t : UnitAddCircle) / t ^ s.val
  have hq : ContinuousOn q (Icc d (1 / 2)) := by
    refine (periodicZeta_continuous s).continuousOn.div ?_ ?_
    · exact continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (hd0.trans_le ht.1))
    · intro t ht
      exact (Real.rpow_pos_of_pos (hd0.trans_le ht.1) _).ne'
  obtain ⟨u, hu, -, hmin⟩ := isCompact_Icc.exists_sInf_image_eq_and_le
    (nonempty_Icc.mpr hdhalf) hq
  obtain ⟨v, hv, -, hmax⟩ := isCompact_Icc.exists_sSup_image_eq_and_ge
    (nonempty_Icc.mpr hdhalf) hq
  have hpos (t : ℝ) (ht : t ∈ Icc d (1 / 2)) : 0 < q t :=
    div_pos (periodicZeta_pos s (hd0.trans_le ht.1) (by linarith [ht.2]))
      (Real.rpow_pos_of_pos (hd0.trans_le ht.1) _)
  refine ⟨min (1 / 2) (q u), max (3 / 2) (q v),
    lt_min (by norm_num) (hpos u hu), lt_max_of_lt_left (by norm_num), fun t ht ht1 => ?_⟩
  by_cases htd : t ≤ d
  · obtain ⟨hl, hh⟩ := hsmall t ht htd
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans hl,
      hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  · have hmem : t ∈ Icc d (1 / 2) := ⟨(lt_of_not_ge htd).le, ht1⟩
    have hl := (min_le_right (1 / 2) (q u)).trans (hmin t hmem)
    have hh := (hmax t hmem).trans (le_max_right (3 / 2) (q v))
    exact ⟨(le_div_iff₀ (Real.rpow_pos_of_pos ht _)).mp hl,
      (div_le_iff₀ (Real.rpow_pos_of_pos ht _)).mp hh⟩

/-- Both constants depend only on the exponent, before `N` and `k` are chosen. -/
theorem gapsDisc_gapScale_comparison (s : RieszExponent) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+) (k : ℕ),
      1 ≤ k → k ≤ (N : ℕ) / 2 →
      c * (k : ℝ) ^ (s.val / 2) ≤ gapScale s N k ∧
        gapScale s N k ≤ C * (k : ℝ) ^ (s.val / 2) := by
  obtain ⟨c, C, hc, hC, hb⟩ := gapsDisc_periodicZeta_comparison s
  refine ⟨Real.sqrt c, Real.sqrt C, Real.sqrt_pos.mpr hc, Real.sqrt_pos.mpr hC,
    fun N k hk hkN => ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ht : (k : ℝ) / N ≤ 1 / 2 := by
    apply (div_le_iff₀ hN).mpr
    have : 2 * k ≤ (N : ℕ) := by omega
    have hreal : (2 : ℝ) * k ≤ N := by exact_mod_cast this
    linarith
  obtain ⟨hl, hh⟩ := hb ((k : ℝ) / N) (div_pos hk0 hN) ht
  have hcancel : (N : ℝ) ^ s.val * ((k : ℝ) / N) ^ s.val = (k : ℝ) ^ s.val := by
    rw [Real.div_rpow hk0.le hN.le]
    field_simp
  have hsqrt : Real.sqrt ((k : ℝ) ^ s.val) = (k : ℝ) ^ (s.val / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hk0.le]
    congr 1
    ring
  have hl' := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hN.le s.val)
  have hh' := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hN.le s.val)
  rw [mul_left_comm _ c, hcancel] at hl'
  rw [mul_left_comm _ C, hcancel] at hh'
  simpa only [gapScale, Real.sqrt_mul hc.le, Real.sqrt_mul hC.le, hsqrt] using
    And.intro (Real.sqrt_le_sqrt hl') (Real.sqrt_le_sqrt hh')


/-- Every admissible gap normalization is strictly positive. -/
lemma gapsDisc_gapScale_pos (s : RieszExponent) (N : ℕ+) (k : ℕ)
    (hk : 1 ≤ k) (hkN : k ≤ (N : ℕ) / 2) : 0 < gapScale s N k := by
  obtain ⟨c, C, hc, -, hb⟩ := gapsDisc_gapScale_comparison s
  exact (mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hk) _)).trans_le
    (hb N k hk hkN).1

/-- Diverging block lengths have diverging normalizations, for arbitrary index filters. -/
theorem gapsDisc_gapScale_tendsto_atTop (s : RieszExponent) {ι : Type*} {l : Filter ι}
    (N : ι → ℕ+) (k : ι → ℕ) (hk : Tendsto k l atTop)
    (hvalid : ∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2) :
    Tendsto (fun n => gapScale s (N n) (k n)) l atTop := by
  obtain ⟨c, C, hc, -, hb⟩ := gapsDisc_gapScale_comparison s
  have hpow := (tendsto_rpow_atTop (half_pos s.2.1)).comp
    (tendsto_natCast_atTop_atTop.comp hk : Tendsto (fun n => (k n : ℝ)) l atTop)
  apply tendsto_atTop_mono' l _ (hpow.const_mul_atTop hc)
  filter_upwards [hvalid] with n hn
  exact (hb (N n) (k n) hn.1 hn.2).1

/-- The normalization is sublinear in the block length. -/
theorem gapsDisc_gapScale_div_tendsto_zero (s : RieszExponent) {ι : Type*} {l : Filter ι}
    (N : ι → ℕ+) (k : ι → ℕ) (hk : Tendsto k l atTop)
    (hvalid : ∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2) :
    Tendsto (fun n => gapScale s (N n) (k n) / k n) l (𝓝 0) := by
  obtain ⟨c, C, -, hC, hb⟩ := gapsDisc_gapScale_comparison s
  have hpow : Tendsto (fun n => C * (k n : ℝ) ^ (s.val / 2 - 1)) l (𝓝 0) := by
    have he : 0 < 1 - s.val / 2 := by linarith [s.2.2]
    have h := (tendsto_rpow_neg_atTop he).comp
      (tendsto_natCast_atTop_atTop.comp hk : Tendsto (fun n => (k n : ℝ)) l atTop)
    simpa only [Function.comp_apply, mul_zero,
      show -(1 - s.val / 2) = s.val / 2 - 1 by ring] using h.const_mul C
  apply squeeze_zero' _ _ hpow
  · exact Eventually.of_forall fun n => div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hvalid] with n hn
    have hk0 : (0 : ℝ) < k n := by exact_mod_cast hn.1
    have h := div_le_div_of_nonneg_right (hb (N n) (k n) hn.1 hn.2).2 hk0.le
    rw [Real.rpow_sub hk0, Real.rpow_one]
    simpa only [mul_div_assoc] using h

end Riesz1

end
end
