/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Euler
public import Riesz1.ToMathlib.HurwitzKernel.Reality
public import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-!
# The renormalized symmetric Riesz sum

The Euler limits on `(0,1)` identify the two halves of the symmetric sum.
Changing the real lift by one changes only two endpoint terms, both tending
to zero. This proves the limit in Lemma 2.1 for
all nonintegral real lifts.
-/

public section

open Filter Topology MeasureTheory
namespace Riesz1

lemma tendsto_hurwitzZeta_sub_real (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    Tendsto (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), ((n : ℝ) + x) ^ (-s)) -
      (M : ℝ) ^ (1 - s) / (1 - s)) atTop
      (𝓝 (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (s : ℂ)).re) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (tendsto_hurwitzZeta_sub x hx0 hx1 (s : ℂ) hs (by exact_mod_cast hs1))
  apply h.congr
  intro M
  dsimp only [Function.comp_def]
  have heq : (((∑ n ∈ Finset.range (M + 1), ((n : ℝ) + x) ^ (-s)) -
      (M : ℝ) ^ (1 - s) / (1 - s) : ℝ) : ℂ) =
      (∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-(s : ℂ))) -
        (M : ℂ) ^ (1 - (s : ℂ)) / (1 - (s : ℂ)) := by
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg M) (1 - s)]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Complex.ofReal_cpow (by positivity : 0 ≤ (n : ℝ) + x) (-s)]
    push_cast
    rfl
  exact (congrArg Complex.re heq).symm

lemma sum_symmetric_split (f : ℤ → ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f k =
      (∑ n ∈ Finset.range (M + 1), f (n : ℤ)) +
        ∑ n ∈ Finset.range M, f (-((n : ℤ) + 1)) := by
  induction M with
  | zero => simp
  | succ M h =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_Icc_succ_eq_add_endpoints, h]
    conv_rhs => lhs; rw [Finset.sum_range_succ]
    conv_rhs => rhs; rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

lemma hurwitzZetaEven_re_expression (x : ℝ) (s : ℂ) :
    2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) s).re =
      (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s).re +
      (HurwitzZeta.hurwitzZeta ((1 - x : ℝ) : UnitAddCircle) s).re := by
  have hcoe : ((1 - x : ℝ) : UnitAddCircle) = -(x : UnitAddCircle) := by
    simp
  rw [hcoe, HurwitzZeta.hurwitzZetaEven_eq]
  simp only [Complex.div_ofNat_re, Complex.add_re]
  ring

lemma tendsto_tail_rpow (s : ℝ) (hs : 0 < s) (x : ℝ) :
    Tendsto (fun M : ℕ => |(M : ℝ) + x| ^ (-s)) atTop (𝓝 0) := by
  apply (tendsto_rpow_neg_atTop hs).comp
  exact Filter.tendsto_abs_atTop_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

lemma tendsto_rieszPartialSum_of_mem_Ioo (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun M : ℕ => (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s)) -
      2 * (M : ℝ) ^ (1 - s) / (1 - s)) atTop
      (𝓝 (2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re)) := by
  have hA := tendsto_hurwitzZeta_sub_real x hx0 hx1.le s hs0 hs1.ne
  have hB := tendsto_hurwitzZeta_sub_real (1 - x) (by linarith) (by linarith) s hs0 hs1.ne
  have htail : Tendsto (fun M : ℕ => ((M : ℝ) + (1 - x)) ^ (-s)) atTop (𝓝 0) := by
    apply (tendsto_tail_rpow s hs0 (1 - x)).congr
    intro M
    rw [abs_of_pos (by positivity)]
  have h := (hA.add hB).sub htail
  rw [sub_zero, ← hurwitzZetaEven_re_expression x (s : ℂ)] at h
  apply h.congr
  intro M
  rw [sum_symmetric_split]
  have hpos : ∀ n : ℕ, |((n : ℤ) : ℝ) + x| ^ (-s) = ((n : ℝ) + x) ^ (-s) := by
    intro n
    rw [Int.cast_natCast, abs_of_pos (by positivity)]
  have hneg : ∀ n : ℕ, |((-((n : ℤ) + 1) : ℤ) : ℝ) + x| ^ (-s) =
      ((n : ℝ) + (1 - x)) ^ (-s) := by
    intro n
    rw [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_neg (by linarith [Nat.cast_nonneg (α := ℝ) n])]
    congr 1
    ring
  simp_rw [hpos, hneg]
  rw [Finset.sum_range_succ (f := fun n : ℕ => ((n : ℝ) + (1 - x)) ^ (-s))]
  ring

lemma sum_symmetric_shift (f : ℤ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f (k + 1)) -
      (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f k) = f ((M : ℤ) + 1) - f (-(M : ℤ)) := by
  rw [← Finset.sum_sub_distrib, sum_symmetric_split]
  have hp := Finset.sum_range_sub (fun n : ℕ => f (n : ℤ)) (M + 1)
  have hn := Finset.sum_range_sub' (fun n : ℕ => f (-(n : ℤ))) M
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hp hn
  have heq : (fun n : ℕ => f (-((n : ℤ) + 1) + 1) - f (-((n : ℤ) + 1))) =
      (fun n : ℕ => f (-(n : ℤ)) - f (-((n : ℤ) + 1))) := by
    funext n
    congr 2
    ring
  rw [heq, hp, hn]
  ring_nf

/-- The symmetric integer sum with its divergent integral term subtracted. -/
@[expose] noncomputable def hurwitzSymmetricSum (s x : ℝ) : ℕ → ℝ := fun M =>
  (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s)) -
    2 * (M : ℝ) ^ (1 - s) / (1 - s)

lemma symmetricSum_add_one_sub (s x : ℝ) (M : ℕ) :
    hurwitzSymmetricSum s (x + 1) M - hurwitzSymmetricSum s x M =
      |(M : ℝ) + (x + 1)| ^ (-s) - |(M : ℝ) - x| ^ (-s) := by
  have h := sum_symmetric_shift (fun k : ℤ => |(k : ℝ) + x| ^ (-s)) M
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast, Int.cast_neg] at h
  have heq : (fun k : ℤ => |(k : ℝ) + 1 + x| ^ (-s)) =
      (fun k : ℤ => |(k : ℝ) + (x + 1)| ^ (-s)) := by
    funext k
    congr 2
    ring
  rw [heq, show -(M : ℝ) + x = -((M : ℝ) - x) by ring, abs_neg] at h
  rw [show (M : ℝ) + 1 + x = (M : ℝ) + (x + 1) by ring] at h
  unfold hurwitzSymmetricSum
  linear_combination h

lemma symmetricSum_add_one_tendsto_iff (s : ℝ) (hs : 0 < s) (x L : ℝ) :
    Tendsto (hurwitzSymmetricSum s (x + 1)) atTop (𝓝 L) ↔
      Tendsto (hurwitzSymmetricSum s x) atTop (𝓝 L) := by
  have hz : Tendsto (fun M => hurwitzSymmetricSum s (x + 1) M - hurwitzSymmetricSum s x M)
      atTop (𝓝 0) := by
    have h := (tendsto_tail_rpow s hs (x + 1)).sub (tendsto_tail_rpow s hs (-x))
    simpa only [sub_self, ← sub_eq_add_neg, symmetricSum_add_one_sub] using h
  constructor
  · intro h
    have hh := h.sub hz
    simpa only [sub_zero, sub_sub_cancel] using hh
  · intro h
    have hh := h.add hz
    simpa only [add_zero, add_sub_cancel] using hh

/-- The renormalized symmetric sum defining the kernel converges to the even Hurwitz
function. -/
theorem tendsto_rieszPartialSum (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ)
    (hx : (x : UnitAddCircle) ≠ 0) :
    Tendsto (fun M : ℕ => (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s)) -
      2 * (M : ℝ) ^ (1 - s) / (1 - s)) atTop
      (𝓝 (2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re)) := by
  have hfract : 0 < Int.fract x := by
    apply lt_of_le_of_ne (Int.fract_nonneg x)
    intro h
    apply hx
    have hcoe := AddCircle.coe_fract x
    rw [← h, AddCircle.coe_zero] at hcoe
    exact hcoe.symm
  let L := 2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re
  have hbase : Tendsto (hurwitzSymmetricSum s (Int.fract x)) atTop (𝓝 L) := by
    unfold hurwitzSymmetricSum
    simpa only [hurwitzSymmetricSum, AddCircle.coe_fract, L] using
      tendsto_rieszPartialSum_of_mem_Ioo s hs0 hs1 (Int.fract x) hfract (Int.fract_lt_one x)
  have hshift (k : ℤ) : Tendsto (hurwitzSymmetricSum s (Int.fract x + k)) atTop (𝓝 L) := by
    induction k using Int.induction_on with
    | zero => simpa only [Int.cast_zero, add_zero] using hbase
    | succ k hk =>
      simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one, ← add_assoc] using
        (symmetricSum_add_one_tendsto_iff s hs0 (Int.fract x + k) L).mpr hk
    | pred k hk =>
      apply (symmetricSum_add_one_tendsto_iff s hs0 (Int.fract x + (-(k : ℤ) - 1 : ℤ)) L).mp
      convert hk using 1
      push_cast
      congr 1
      ring
  have h := hshift ⌊x⌋
  unfold hurwitzSymmetricSum at h
  simpa only [Int.fract_add_floor, hurwitzSymmetricSum, L] using h

end Riesz1
