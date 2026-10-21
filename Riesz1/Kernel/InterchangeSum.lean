/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Symmetric
public import Riesz1.ToMathlib.MollifierPointwise.Basic
public import Riesz1.Frozen.RieszRepresentative
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic

/-!
# The centered series of the interchange lemma

The right-hand side of the interchange lemma is the centered series
`∑_k (|x - k|^{-s} - ∫_0^1 |y - k|^{-s} dy)`. This file identifies it with the renormalized
symmetric sum `lim_M (∑_{|k| ≤ M} |k + x|^{-s} - 2M^{1-s}/(1-s))`, whose limit
`Riesz1.tendsto_rieszPartialSum` identifies with `2 Re ζ_even(x, s)`, the value of
`rieszRepresentative` at `x`.

The key identities are:
* the reflection `k ↦ -k` on the symmetric index set.
* the adjacent-interval evaluation `∑_{|k| ≤ M} ∫_0^1 |y - k|^{-s} dy = (M^{1-s} + (M+1)^{1-s})/(1-s)`.
* the decay `(M+1)^{1-s} - M^{1-s} → 0`.

Main results:
* `Riesz1.sum_gaussAverage_eq`: the symmetric sum of the one-period integrals.
* `Riesz1.tendsto_rpow_succ_sub`: the decay of `(M+1)^{1-s} - M^{1-s}`.
* `Riesz1.tsum_centered_eq_riesz`: `∑_k (|x-k|^{-s} - ∫_0^1 |y-k|^{-s} dy) = rieszRepresentative`.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- The interval integrability of `|u|^{-s}` on every interval, for `s < 1`. -/
lemma intervalIntegrable_abs_rpow_neg {s : ℝ} (hs : s < 1) (c d : ℝ) :
    IntervalIntegrable (fun u : ℝ => |u| ^ (-s)) volume c d := by
  rw [intervalIntegrable_iff]
  have hR0 : (0 : ℝ) ≤ |c| + |d| := by positivity
  have hc : c ∈ Icc (-(|c| + |d|)) (|c| + |d|) :=
    ⟨by linarith [neg_abs_le c, abs_nonneg d], by linarith [le_abs_self c, abs_nonneg d]⟩
  have hd : d ∈ Icc (-(|c| + |d|)) (|c| + |d|) :=
    ⟨by linarith [neg_abs_le d, abs_nonneg c], by linarith [le_abs_self d, abs_nonneg c]⟩
  exact (integrableOn_abs_rpow (by linarith : -1 < -s) hR0).mono_set
    (uIoc_subset_uIcc.trans (uIcc_subset_Icc hc hd))

/-- The integral `∫_a^b |u|^{-s} du = (b^{1-s} - a^{1-s})/(1-s)` for `0 ≤ a ≤ b`. -/
lemma integral_abs_rpow_neg_Icc {s : ℝ} (hs1 : s < 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ u in a..b, |u| ^ (-s) = (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  have hcongr : ∫ u in a..b, |u| ^ (-s) = ∫ u in a..b, u ^ (-s) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le hab] at hu
    show |u| ^ (-s) = u ^ (-s)
    rw [abs_of_nonneg (ha.trans hu.1)]
  rw [hcongr, integral_rpow (Or.inl (by linarith))]
  rw [show -s + 1 = 1 - s by ring]

/-- The integral `∫_{-1}^0 |u|^{-s} du = 1/(1-s)`. -/
lemma integral_abs_rpow_neg_left {s : ℝ} (hs1 : s < 1) :
    ∫ u in (-1 : ℝ)..0, |u| ^ (-s) = 1 / (1 - s) := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (fun u : ℝ => |u| ^ (-s))
  simp only [abs_neg, neg_zero] at h
  rw [← h, integral_abs_rpow_neg_Icc hs1 le_rfl zero_le_one, Real.one_rpow,
    Real.zero_rpow (sub_pos.2 hs1).ne', sub_zero]

/-- The one-period integral of `|y - n|^{-s}` over `[0, 1]` equals the integral over `[n-1, n]`. -/
lemma integral_abs_sub_nat {s : ℝ} (n : ℕ) :
    ∫ y in (0 : ℝ)..1, |y - ((n : ℤ) : ℝ)| ^ (-s) = ∫ u in ((n : ℝ) - 1)..(n : ℝ), |u| ^ (-s) := by
  rw [Int.cast_natCast]
  have h := intervalIntegral.integral_comp_sub_left (fun u : ℝ => |u| ^ (-s)) (a := 0) (b := 1)
    (n : ℝ)
  simp only [sub_zero] at h
  refine (intervalIntegral.integral_congr (fun y _ => ?_)).trans h
  show |y - (n : ℝ)| ^ (-s) = |(n : ℝ) - y| ^ (-s)
  rw [abs_sub_comm]

/-- The one-period integral of `|y + (n+1)|^{-s}` over `[0, 1]` equals the integral over
`[n+1, n+2]`. -/
lemma integral_abs_sub_neg_nat {s : ℝ} (n : ℕ) :
    ∫ y in (0 : ℝ)..1, |y - (((-((n : ℤ) + 1)) : ℤ) : ℝ)| ^ (-s) =
      ∫ u in ((n : ℝ) + 1)..((n : ℝ) + 1 + 1), |u| ^ (-s) := by
  have h := intervalIntegral.integral_comp_add_left (fun u : ℝ => |u| ^ (-s)) (a := 0) (b := 1)
    ((n : ℝ) + 1)
  simp only [add_zero] at h
  refine (intervalIntegral.integral_congr (fun y _ => ?_)).trans h
  show |y - (((-((n : ℤ) + 1)) : ℤ) : ℝ)| ^ (-s) = |((n : ℝ) + 1) + y| ^ (-s)
  congr 2
  push_cast
  ring

/-- The symmetric sum of the one-period integrals `∫_0^1 |y - k|^{-s} dy` over `|k| ≤ M`
equals `(M^{1-s} + (M+1)^{1-s})/(1-s)`. -/
lemma sum_integral_abs_sub_eq {s : ℝ} (hs1 : s < 1) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s) =
      ((M : ℝ) ^ (1 - s) + ((M : ℝ) + 1) ^ (1 - s)) / (1 - s) := by
  have hp : (1 - s) ≠ 0 := (sub_pos.2 hs1).ne'
  -- The nonnegative half: `k = n ≥ 0` gives the intervals `[n-1, n]`, which tile `[-1, M]`.
  have hsplit1 : ∑ n ∈ Finset.range (M + 1), ∫ y in (0 : ℝ)..1, |y - ((n : ℤ) : ℝ)| ^ (-s) =
      ∫ u in (-1 : ℝ)..(M : ℝ), |u| ^ (-s) := by
    rw [Finset.sum_congr rfl (fun n _ => integral_abs_sub_nat (s := s) n)]
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := fun u : ℝ => |u| ^ (-s))
      (μ := volume) (a := fun j : ℕ => (j : ℝ) - 1) (n := M + 1)
      (fun k _ => intervalIntegrable_abs_rpow_neg hs1 _ _)
    simpa using h
  -- The negative half: `k = -(n+1) ≤ -1` gives the intervals `[n+1, n+2]`, tiling `[1, M+1]`.
  have hsplit2 : ∑ n ∈ Finset.range M,
      ∫ y in (0 : ℝ)..1, |y - (((-((n : ℤ) + 1)) : ℤ) : ℝ)| ^ (-s) =
        ∫ u in (1 : ℝ)..((M : ℝ) + 1), |u| ^ (-s) := by
    rw [Finset.sum_congr rfl (fun n _ => integral_abs_sub_neg_nat (s := s) n)]
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := fun u : ℝ => |u| ^ (-s))
      (μ := volume) (a := fun j : ℕ => (j : ℝ) + 1) (n := M)
      (fun k _ => intervalIntegrable_abs_rpow_neg hs1 _ _)
    simpa [add_assoc] using h
  have hsum := sum_symmetric_split (fun k : ℤ => ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s)) M
  rw [hsum, hsplit1, hsplit2]
  -- Split `∫_{-1}^M` at zero and evaluate each piece.
  have hI1 : IntervalIntegrable (fun u : ℝ => |u| ^ (-s)) volume (-1) 0 :=
    intervalIntegrable_abs_rpow_neg hs1 _ _
  have hI2 : IntervalIntegrable (fun u : ℝ => |u| ^ (-s)) volume 0 (M : ℝ) :=
    intervalIntegrable_abs_rpow_neg hs1 _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2,
    integral_abs_rpow_neg_left hs1,
    integral_abs_rpow_neg_Icc hs1 le_rfl (Nat.cast_nonneg M),
    integral_abs_rpow_neg_Icc hs1 zero_le_one (by linarith [Nat.cast_nonneg (α := ℝ) M])]
  rw [Real.one_rpow, Real.zero_rpow hp]
  ring

/-- The reflection `k ↦ -k` on the symmetric index set: `∑_{|k|≤M} |x - k|^{-s} = ∑_{|k|≤M}
|k + x|^{-s}`. -/
lemma sum_abs_sub_eq_reflect (x s : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |x - (k : ℝ)| ^ (-s) =
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s) := by
  refine Finset.sum_nbij' (fun k : ℤ => -k) (fun k : ℤ => -k) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    omega
  · intro a _
    exact neg_neg a
  · intro a _
    exact neg_neg a
  · intro a _
    rw [show (((-a : ℤ)) : ℝ) + x = x - a by push_cast; ring]

/-- The decay `(M+1)^{1-s} - M^{1-s} → 0` for `0 < s < 1`. -/
lemma tendsto_rpow_succ_sub {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (1 - s) - (M : ℝ) ^ (1 - s)) atTop (𝓝 0) := by
  have hup : Tendsto (fun M : ℕ => (1 - s) * (M : ℝ) ^ (-s)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hs0).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul (1 - s)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hm0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hmono : (M : ℝ) ^ (1 - s) ≤ ((M : ℝ) + 1) ^ (1 - s) :=
      Real.rpow_le_rpow hm0.le (by linarith) (by linarith)
    show (0 : ℝ) ≤ ((M : ℝ) + 1) ^ (1 - s) - (M : ℝ) ^ (1 - s)
    linarith
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hm0 : (0 : ℝ) < M := by linarith
    have hp0 : (0 : ℝ) ≤ 1 - s := by linarith
    have hp1 : (1 - s) ≤ 1 := by linarith
    have hfac : ((M : ℝ) + 1) ^ (1 - s) = (M : ℝ) ^ (1 - s) * (1 + 1 / (M : ℝ)) ^ (1 - s) := by
      rw [← Real.mul_rpow hm0.le (by positivity)]
      congr 1
      field_simp
    have hinv : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    have hb := rpow_one_add_le_one_add_mul_self (s := 1 / (M : ℝ)) (by linarith) hp0 hp1
    have hle := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hm0.le (1 - s))
    have hneg : (M : ℝ) ^ (-s) = (M : ℝ) ^ (1 - s) / M := by
      rw [← Real.rpow_sub_one hm0.ne' (1 - s)]
      congr 1
      ring
    have e2 : (M : ℝ) ^ (1 - s) * (1 + (1 - s) * (1 / (M : ℝ))) =
        (M : ℝ) ^ (1 - s) + (1 - s) * ((M : ℝ) ^ (1 - s) / M) := by
      ring
    show ((M : ℝ) + 1) ^ (1 - s) - (M : ℝ) ^ (1 - s) ≤ (1 - s) * (M : ℝ) ^ (-s)
    rw [hfac, hneg]
    linarith

/-- The centered sum over `|k| ≤ M`, with the one-period integrals subtracted, equals the
renormalized symmetric sum minus the decay term. -/
lemma sum_centered_eq {s x : ℝ} (hs1 : s < 1) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (|x - (k : ℝ)| ^ (-s) - ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s)) =
      (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s)) -
        2 * (M : ℝ) ^ (1 - s) / (1 - s) -
        (((M : ℝ) + 1) ^ (1 - s) - (M : ℝ) ^ (1 - s)) / (1 - s) := by
  rw [Finset.sum_sub_distrib, sum_abs_sub_eq_reflect x s M, sum_integral_abs_sub_eq hs1 M]
  ring

/-- The point `x ∈ (0, 1)` is nonzero in the circle `ℝ / ℤ`. -/
lemma coe_ne_zero_of_mem_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : (x : UnitAddCircle) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h
  rw [zsmul_eq_mul, mul_one] at hn
  have h1 : (0 : ℝ) < n := hn ▸ hx0
  have h2 : (n : ℝ) < 1 := hn ▸ hx1
  have h3 : (0 : ℤ) < n := by exact_mod_cast h1
  have h4 : n < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- The centered series `∑_k (|x - k|^{-s} - ∫_0^1 |y - k|^{-s} dy)` converges to
`2 Re ζ_even(x, s) = rieszRepresentative s x`, for `0 < s < 1` and `0 < x < 1`, whenever it is
summable. -/
theorem tsum_centered_eq_riesz {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (hb : Summable fun k : ℤ => |x - (k : ℝ)| ^ (-s) - ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s)) :
    ∑' k : ℤ, (|x - (k : ℝ)| ^ (-s) - ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s)) =
      2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re := by
  -- Along the symmetric index sets `|k| ≤ M`, the partial sums converge to the tsum.
  have hmono : Monotone fun M : ℕ => Finset.Icc (-(M : ℤ)) (M : ℤ) := fun M N hMN =>
    Finset.Icc_subset_Icc (by omega) (by omega)
  have hexh : ∀ k : ℤ, ∃ M : ℕ, k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := fun k =>
    ⟨k.natAbs, by rw [Finset.mem_Icc]; omega⟩
  have hlim1 : Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      (|x - (k : ℝ)| ^ (-s) - ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s))) atTop
      (𝓝 (∑' k : ℤ, (|x - (k : ℝ)| ^ (-s) - ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s)))) :=
    hb.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hexh)
  have hlim2 : Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      (|x - (k : ℝ)| ^ (-s) - ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s))) atTop
      (𝓝 (2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re)) := by
    simp_rw [sum_centered_eq hs1]
    have h := (tendsto_rieszPartialSum s hs0 hs1 x (coe_ne_zero_of_mem_Ioo hx0 hx1)).sub
      ((tendsto_rpow_succ_sub hs0 hs1).div_const (1 - s))
    simpa using h
  exact tendsto_nhds_unique hlim1 hlim2

end Riesz1
