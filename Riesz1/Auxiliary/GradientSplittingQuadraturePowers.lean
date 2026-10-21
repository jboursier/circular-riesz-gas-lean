/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Exponent arithmetic for partial-window quadrature

The quadrature part of Lemma 5.7: the odd tails cost
`K^(2-s-a) n^(-s) r^(-1+3s/2)`. The two ranges of `s` are treated explicitly,
including `s = 2/3`. The floor costs at most `2^s`.
-/

@[expose] public section

namespace Riesz1

/-- The restrictions on `γ` imply both exponent conditions used by the odd tails. -/
lemma gradPartial_gamma_exponents {s a γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha : 0 ≤ a) (hγ4 : 4 ≤ γ) (hγs : 2 / s ≤ γ) :
    2 ≤ γ * s ∧ 1 - γ * s ≤ 0 ∧ 1 + s / 2 - a - γ * s ≤ 0 ∧
      2 - s - a + γ * (-1 + s / 2) ≤ 0 := by
  have hg : 2 ≤ γ * s := (div_le_iff₀ hs0).mp hγs
  have hc : γ * (-1 + s / 2) ≤ 4 * (-1 + s / 2) :=
    mul_le_mul_of_nonpos_right hγ4 (by linarith)
  exact ⟨hg, by linarith, by linarith, by linarith⟩

/-- Replacing `n` by `M = K^γ` in a negative power costs at most `2^s`. -/
lemma gradPartial_floor_power_le {s K γ n : ℝ} (hs : 0 ≤ s) (hK : 0 < K)
    (_hn : 0 < n) (hfloor : K ^ γ ≤ 2 * n) :
    n ^ (-s) ≤ 2 ^ s * K ^ (-(γ * s)) := by
  have hM : 0 < K ^ γ / 2 := by positivity
  calc n ^ (-s) ≤ (K ^ γ / 2) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hM (by linarith) (by linarith)
    _ = 2 ^ s * K ^ (-(γ * s)) := by
      rw [Real.div_rpow (Real.rpow_nonneg hK.le _) (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
        ← Real.rpow_mul hK.le]
      rw [show γ * -s = -(γ * s) by ring, mul_comm]

/-- Near the microscopic core the odd tail is bounded by the first target term's ratio. -/
lemma gradPartial_inner_tail_ratio {s γ K n : ℝ} (hs : 0 ≤ s) (hγs : 1 ≤ γ * s)
    (hK : 1 ≤ K) (hn : 0 < n) (hfloor : K ^ γ ≤ 2 * n) :
    K * n ^ (-s) ≤ 2 ^ s := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hfloor' := gradPartial_floor_power_le hs hK0 hn hfloor
  calc K * n ^ (-s) ≤ K * (2 ^ s * K ^ (-(γ * s))) :=
      mul_le_mul_of_nonneg_left hfloor' hK0.le
    _ = 2 ^ s * K ^ (1 - γ * s) := by
      rw [Real.rpow_sub hK0, Real.rpow_one, Real.rpow_neg hK0.le]
      ring_nf
    _ ≤ 2 ^ s * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hK (by linarith)) (by positivity)
    _ = _ := mul_one _

/-- The outer odd-tail ratio, with the two monotonicity cases from the paper. -/
theorem gradPartial_outer_tail_ratio {s a γ K n r : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha : 0 ≤ a) (hγ4 : 4 ≤ γ) (hγs : 2 / s ≤ γ)
    (hK : 1 ≤ K) (hn : 0 < n) (hfloor : K ^ γ ≤ 2 * n)
    (hrK : K ≤ r) (hrM : r ≤ K ^ γ) :
    K ^ (2 - s - a) * n ^ (-s) * r ^ (-1 + 3 * s / 2) ≤ 2 ^ s := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hr0 : 0 < r := hK0.trans_le hrK
  have hfloor' := gradPartial_floor_power_le hs0.le hK0 hn hfloor
  have hexp := gradPartial_gamma_exponents hs0 hs1 ha hγ4 hγs
  have hbase : K ^ (2 - s - a) * n ^ (-s) * r ^ (-1 + 3 * s / 2) ≤
      2 ^ s * (K ^ (2 - s - a - γ * s) * r ^ (-1 + 3 * s / 2)) := by
    calc _ ≤ K ^ (2 - s - a) * (2 ^ s * K ^ (-(γ * s))) * r ^ (-1 + 3 * s / 2) := by
          gcongr
      _ = _ := by
        have he : K ^ (2 - s - a - γ * s) = K ^ (2 - s - a) * K ^ (-(γ * s)) := by
          rw [← Real.rpow_add hK0]; congr 1
        rw [he]
        ring_nf
  refine hbase.trans ?_
  apply mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ 2 ^ s)
  by_cases hs : s ≤ 2 / 3
  · have hr : r ^ (-1 + 3 * s / 2) ≤ K ^ (-1 + 3 * s / 2) :=
      Real.rpow_le_rpow_of_nonpos hK0 hrK (by linarith)
    calc _ ≤ K ^ (2 - s - a - γ * s) * K ^ (-1 + 3 * s / 2) := by gcongr
      _ = K ^ (1 + s / 2 - a - γ * s) := by rw [← Real.rpow_add hK0]; congr 1; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK hexp.2.2.1
  · have hr : r ^ (-1 + 3 * s / 2) ≤ (K ^ γ) ^ (-1 + 3 * s / 2) :=
      Real.rpow_le_rpow hr0.le hrM (by linarith)
    calc _ ≤ K ^ (2 - s - a - γ * s) * (K ^ γ) ^ (-1 + 3 * s / 2) := by gcongr
      _ = K ^ (2 - s - a + γ * (-1 + s / 2)) := by
        rw [← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]; congr 1; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK hexp.2.2.2

/-- The remainder-strip power is uniformly bounded, including the floor endpoint. -/
lemma gradPartial_strip_power_le {s n r : ℝ} (hs : 0 ≤ s) (hn : 1 ≤ n) (hr : r ≤ n)
    (hr0 : 0 ≤ r) : (1 + r) ^ (s / 2) * n ^ (-s) ≤ 2 ^ (s / 2) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  calc (1 + r) ^ (s / 2) * n ^ (-s)
      ≤ (2 * n) ^ (s / 2) * n ^ (-s) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    _ = 2 ^ (s / 2) * n ^ (-s / 2) := by
      rw [Real.mul_rpow (by norm_num) hn0.le, mul_assoc, ← Real.rpow_add hn0]
      congr 1
      ring_nf
    _ ≤ 2 ^ (s / 2) * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)) (by positivity)
    _ = _ := mul_one _

end Riesz1
