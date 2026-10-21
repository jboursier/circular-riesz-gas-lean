/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellKernel

/-!
# Scalar quadrature of the averaged kernel

The quadrature part of Lemma B.1. For the averaged kernel `q` of
`BellKernel.lean`, the lattice sum `∑_{k=1}^{N-1} q(k)` is compared with the integral
`∫_0^N q`. The error is controlled by `2 ∫_0^{1/2} |q| + ∫_{1/2}^{N-1/2} |q'|`, and this is at
most `C_s A`.

The proof splits `∫_0^N q` into `∫_0^{1/2} q`, `∫_{1/2}^{N-1/2} q` and `∫_{N-1/2}^N q`. The last
piece equals the first by reflection. The middle piece is a sum over unit cells centred at `k`,
and on each cell `q` differs from its value at `k` by at most the integral of `|q'|` over the cell.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace Riesz1

/-- A function with the bound `|F x| ≤ g x` on `(a, b)`, where `g` is integrable and `F` is
continuous on `(a, b)`, is integrable on `[a, b]`. The endpoint `b` is excluded from the bound
and enters only through the almost everywhere condition `x ≠ b`. -/
lemma intervalIntegrable_of_bound {F g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Ioo a b)) (hg : IntervalIntegrable g volume a b)
    (hbd : ∀ x ∈ Ioo a b, |F x| ≤ g x) (hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b) :
    IntervalIntegrable F volume a b := by
  refine IntervalIntegrable.mono_fun' hg ?_ ?_
  · rw [Set.uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hF.aestronglyMeasurable measurableSet_Ioo
  · rw [Set.uIoc_of_le hab]
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hae] with x hx1 hx2
    show ‖F x‖ ≤ g x
    rw [Real.norm_eq_abs]
    exact hbd x ⟨hx1.1, lt_of_le_of_ne hx1.2 hx2⟩

/-- A real `x` differs from a fixed `c` for almost every `x`. -/
lemma ae_ne_const (c : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
  rw [ae_iff]
  simp

/-- The integral of an interval integrable function does not depend on the orientation of the
interval once the integrability is transferred. -/
lemma intervalIntegrable_flip {f : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable f volume a b) :
    IntervalIntegrable f volume b a := by
  rw [intervalIntegrable_iff] at h ⊢
  rwa [Set.uIoc_comm]

/-- The fundamental theorem of calculus with the bound `|f y - f x| ≤ ∫_a^b |f'|` for points
`x, y` of an interval `[a, b]` on which `f` has derivative `f'`. -/
lemma abs_sub_le_integral_abs_of_hasDerivAt {f f' : ℝ → ℝ} {a b x y : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (hc : ContinuousOn f' (Icc a b))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f y - f x| ≤ ∫ t in a..b, |f' t| := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hsub : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
  have hint : IntervalIntegrable f' volume x y := (hc.mono hsub).intervalIntegrable
  have hFTC : ∫ t in x..y, f' t = f y - f x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub ht)) hint
  have hintb : IntervalIntegrable (fun t => |f' t|) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (continuous_abs.comp_continuousOn hc)
  rw [← hFTC]
  rcases le_total x y with hxy | hyx
  · calc |∫ t in x..y, f' t| ≤ ∫ t in x..y, |f' t| :=
          intervalIntegral.abs_integral_le_integral_abs hxy
      _ ≤ ∫ t in a..b, |f' t| :=
          intervalIntegral.integral_mono_interval hx.1 hxy hy.2
            (ae_of_all _ fun t => abs_nonneg _) hintb
  · rw [intervalIntegral.integral_symm y x, abs_neg]
    calc |∫ t in y..x, f' t| ≤ ∫ t in y..x, |f' t| :=
          intervalIntegral.abs_integral_le_integral_abs hyx
      _ ≤ ∫ t in a..b, |f' t| :=
          intervalIntegral.integral_mono_interval hy.1 hyx hx.2
            (ae_of_all _ fun t => abs_nonneg _) hintb

/-- The unit cells `[k - 1/2, k + 1/2]` for `1 ≤ k ≤ N - 1` tile `[1/2, N - 1/2]`. -/
lemma sum_cells_eq (F : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hF : ∀ k ∈ Finset.Icc 1 (N - 1),
      IntervalIntegrable F volume ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :
    ∑ k ∈ Finset.Icc 1 (N - 1), ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), F y
      = ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), F y := by
  have hIcc : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := F)
    (a := fun j : ℕ => (j : ℝ) + 1 / 2) (n := N - 1)
    (fun j hj => by
      have hm : j + 1 ∈ Finset.Icc 1 (N - 1) := by
        simp only [Finset.mem_Icc]
        omega
      convert hF (j + 1) hm using 2
      push_cast
      ring)
  have hsum : ∑ k ∈ Finset.Icc 1 (N - 1), ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), F y
      = ∑ j ∈ Finset.range (N - 1),
          ∫ x in ((j : ℝ) + 1 / 2)..(((j + 1 : ℕ) : ℝ) + 1 / 2), F x := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have e1 : ((1 + j : ℕ) : ℝ) - 1 / 2 = (j : ℝ) + 1 / 2 := by push_cast; ring
    have e2 : ((1 + j : ℕ) : ℝ) + 1 / 2 = ((j + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
    rw [e1, e2]
  rw [hsum, hadj]
  have h0 : ((0 : ℕ) : ℝ) + 1 / 2 = 1 / 2 := by norm_num
  have hN' : ((N - 1 : ℕ) : ℝ) + 1 / 2 = (N : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub hN]
    push_cast
    ring
  rw [h0, hN']

/-- For `a, b > 0` the power `min a b ^ q` is at most `a ^ q + b ^ q`. -/
lemma rpow_min_le_add (a b q : ℝ) (ha : 0 < a) (hb : 0 < b) :
    min a b ^ q ≤ a ^ q + b ^ q := by
  rcases min_choice a b with h | h <;> rw [h]
  · linarith [Real.rpow_nonneg hb.le q]
  · linarith [Real.rpow_nonneg ha.le q]

/-- The quadrature bound for a function `q` with the properties of the averaged kernel:
continuity on `(0, N)`, reflection about `N/2`, a derivative `q'` continuous on `(0, N)`, and
integrability near `0` and `N`. -/
lemma bell_quadrature_sum_bound {N : ℕ} (hN : 1 ≤ N) {q : ℝ → ℝ}
    (hqc : ContinuousOn q (Ioo 0 (N : ℝ)))
    (hrefl : ∀ y ∈ Ioo (0 : ℝ) N, q ((N : ℝ) - y) = q y)
    (hd : ∀ y ∈ Ioo (0 : ℝ) N, HasDerivAt q (deriv q y) y)
    (hq'c : ContinuousOn (deriv q) (Ioo 0 (N : ℝ)))
    (hint0 : IntervalIntegrable q volume 0 (1 / 2))
    (hintN : IntervalIntegrable q volume ((N : ℝ) - 1 / 2) N) :
    |(∑ k ∈ Finset.Icc 1 (N - 1), q (k : ℝ)) - ∫ y in (0 : ℝ)..(N : ℝ), q y|
      ≤ 2 * (∫ y in (0 : ℝ)..(1 / 2), |q y|)
        + ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), |deriv q y| := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hIcc_sub : Icc (1 / 2 : ℝ) ((N : ℝ) - 1 / 2) ⊆ Ioo 0 (N : ℝ) :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- Each cell lies in `[1/2, N - 1/2]`.
  have hcell : ∀ k ∈ Finset.Icc 1 (N - 1),
      Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) ⊆ Icc (1 / 2 : ℝ) ((N : ℝ) - 1 / 2) := by
    intro k hk y hy
    rw [Finset.mem_Icc] at hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hk2 : (k : ℝ) + 1 ≤ N := by exact_mod_cast (show k + 1 ≤ N by omega)
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcellq : ∀ k ∈ Finset.Icc 1 (N - 1),
      IntervalIntegrable q volume ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := by
    intro k hk
    exact ContinuousOn.intervalIntegrable_of_Icc (by linarith [hk])
      (hqc.mono (((hcell k hk).trans (Icc_subset_Icc le_rfl le_rfl)).trans hIcc_sub))
  have hcellabs : ∀ k ∈ Finset.Icc 1 (N - 1),
      IntervalIntegrable (fun y => |deriv q y|) volume ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    exact ContinuousOn.intervalIntegrable_of_Icc (by linarith)
      (continuous_abs.comp_continuousOn (hq'c.mono ((hcell k hk).trans hIcc_sub)))
  have hS1 := sum_cells_eq q hN hcellq
  have hS2 : ∑ k ∈ Finset.Icc 1 (N - 1), ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv q y|
      = ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), |deriv q y| :=
    sum_cells_eq (fun y => |deriv q y|) hN hcellabs
  -- Per-cell bound: `|q(k) - ∫_cell q| ≤ ∫_cell |q'|`.
  have hcellbound : ∀ k ∈ Finset.Icc 1 (N - 1),
      |q (k : ℝ) - ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), q y|
        ≤ ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv q y| := by
    intro k hk
    have hsubOO := (hcell k hk).trans hIcc_sub
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkmem : (k : ℝ) ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := ⟨by linarith, by linarith⟩
    have hint_eq : (q (k : ℝ) - ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), q y)
        = ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), (q (k : ℝ) - q y) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hcellq k hk),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hint_eq]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (k : ℝ) - 1 / 2) (b := (k : ℝ) + 1 / 2)
      (C := ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv q y|)
      (f := fun y => q (k : ℝ) - q y) (fun y hy => by
        rw [Set.uIoc_of_le (by linarith)] at hy
        have hyc : y ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := Ioc_subset_Icc_self hy
        show ‖q (k : ℝ) - q y‖ ≤ _
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact abs_sub_le_integral_abs_of_hasDerivAt
          (fun t ht => hd t (hsubOO ht)) (hq'c.mono hsubOO) hkmem hyc)
    have hlen : |((k : ℝ) + 1 / 2) - ((k : ℝ) - 1 / 2)| = 1 := by
      rw [show ((k : ℝ) + 1 / 2) - ((k : ℝ) - 1 / 2) = 1 by ring, abs_one]
    rw [Real.norm_eq_abs, hlen, mul_one] at hb
    exact hb
  have hsum_bd : |(∑ k ∈ Finset.Icc 1 (N - 1), q (k : ℝ))
      - ∑ k ∈ Finset.Icc 1 (N - 1), ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), q y|
      ≤ ∑ k ∈ Finset.Icc 1 (N - 1), ∫ y in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv q y| := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hcellbound)
  rw [hS1, hS2] at hsum_bd
  -- Splitting `∫_0^N q` and reflecting the last piece onto the first.
  have hint_mid : IntervalIntegrable q volume (1 / 2) ((N : ℝ) - 1 / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hqc.mono hIcc_sub)
  have hint_half_N : IntervalIntegrable q volume (1 / 2) N := hint_mid.trans hintN
  have hsplit1 : ∫ y in (0 : ℝ)..(N : ℝ), q y
      = (∫ y in (0 : ℝ)..(1 / 2), q y) + ∫ y in (1 / 2 : ℝ)..(N : ℝ), q y :=
    (intervalIntegral.integral_add_adjacent_intervals hint0 hint_half_N).symm
  have hsplit2 : ∫ y in (1 / 2 : ℝ)..(N : ℝ), q y
      = (∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), q y) + ∫ y in ((N : ℝ) - 1 / 2)..(N : ℝ), q y :=
    (intervalIntegral.integral_add_adjacent_intervals hint_mid hintN).symm
  have hend : ∫ y in ((N : ℝ) - 1 / 2)..(N : ℝ), q y = ∫ y in (0 : ℝ)..(1 / 2), q y := by
    have h := intervalIntegral.integral_comp_sub_left q (N : ℝ) (a := 0) (b := 1 / 2)
    rw [sub_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact hrefl x ⟨hx.1, by linarith [hx.2]⟩
  have key : (∑ k ∈ Finset.Icc 1 (N - 1), q (k : ℝ)) - ∫ y in (0 : ℝ)..(N : ℝ), q y
      = ((∑ k ∈ Finset.Icc 1 (N - 1), q (k : ℝ))
          - ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), q y)
        - 2 * ∫ y in (0 : ℝ)..(1 / 2), q y := by
    rw [hsplit1, hsplit2, hend]
    ring
  have hI0 : |∫ y in (0 : ℝ)..(1 / 2), q y| ≤ ∫ y in (0 : ℝ)..(1 / 2), |q y| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have htwo : |2 * ∫ y in (0 : ℝ)..(1 / 2), q y| = 2 * |∫ y in (0 : ℝ)..(1 / 2), q y| := by
    rw [abs_mul, abs_two]
  rw [key]
  calc _ ≤ |(∑ k ∈ Finset.Icc 1 (N - 1), q (k : ℝ))
          - ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), q y|
        + |2 * ∫ y in (0 : ℝ)..(1 / 2), q y| := abs_sub _ _
    _ ≤ _ := by linarith [hsum_bd, hI0, htwo]

/-- The quadrature part of Lemma B.1. For `0 < s < 1` there is `C > 0`,
depending only on `s`, such that for every integer `N ≥ 1`, every `0 < ℓ ≤ 1` with `Nℓ ≥ 1`, and
every real `ψ ∈ C^∞(ℓ⁻¹𝕋)`, the lattice sum of the averaged kernel `q`
satisfies `|∑_{k=1}^{N-1} q(k) - ∫_0^N q| ≤ 2 ∫_0^{1/2} |q| + ∫_{1/2}^{N-1/2} |q'| ≤ C A`, where
`A = ℓ ‖ψ'‖²_{L²(ℓ⁻¹𝕋)}` is `bellConstant ℓ ψ`. -/
theorem bell_quadrature (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ), 1 ≤ N → 0 < ℓ → ℓ ≤ 1 →
      1 ≤ (N : ℝ) * ℓ → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      |(∑ k ∈ Finset.Icc 1 (N - 1), bellKernel s N ℓ ψ (k : ℝ))
          - ∫ y in (0 : ℝ)..(N : ℝ), bellKernel s N ℓ ψ y|
        ≤ 2 * (∫ y in (0 : ℝ)..(1 / 2), |bellKernel s N ℓ ψ y|)
          + ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), |deriv (bellKernel s N ℓ ψ) y| ∧
      2 * (∫ y in (0 : ℝ)..(1 / 2), |bellKernel s N ℓ ψ y|)
          + ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), |deriv (bellKernel s N ℓ ψ) y|
        ≤ C * bellConstant ℓ ψ := by
  obtain ⟨C1, hC1, hK⟩ := bell_kernel s hs0 hs1
  have hpos1 : 0 < (1 / 2 : ℝ) ^ (1 - s) / (1 - s) :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)
  have hpos2 : 0 < (1 / 2 : ℝ) ^ (-s) / s :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) _) hs0
  refine ⟨C1 * (2 * ((1 / 2 : ℝ) ^ (1 - s) / (1 - s)) + 2 * ((1 / 2 : ℝ) ^ (-s) / s)),
    mul_pos hC1 (by linarith), fun N ℓ ψ hN hℓ0 hℓ1 hNℓ hψ hper => ?_⟩
  obtain ⟨_, hr, hq, hq'⟩ := hK N ℓ ψ hN hℓ0 hℓ1 hNℓ hψ hper
  have hN0 : 0 < N := hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA0 : 0 ≤ bellConstant ℓ ψ := mul_nonneg hℓ0.le (bellEnergy_nonneg hℓ0)
  have hCA : 0 ≤ C1 * bellConstant ℓ ψ := mul_nonneg hC1.le hA0
  have hqc : ContinuousOn (bellKernel s N ℓ ψ) (Ioo 0 (N : ℝ)) := fun y hy =>
    (hasDerivAt_bellKernel hs0 hs1 hN0 hℓ0 hψ hy).continuousAt.continuousWithinAt
  have hd : ∀ y ∈ Ioo (0 : ℝ) N,
      HasDerivAt (bellKernel s N ℓ ψ) (deriv (bellKernel s N ℓ ψ) y) y := by
    intro y hy
    rw [(hasDerivAt_bellKernel hs0 hs1 hN0 hℓ0 hψ hy).deriv]
    exact hasDerivAt_bellKernel hs0 hs1 hN0 hℓ0 hψ hy
  have hq'c : ContinuousOn (deriv (bellKernel s N ℓ ψ)) (Ioo 0 (N : ℝ)) :=
    (continuousOn_bellKernelDeriv hs0 hs1 hN0 hℓ0 hψ).congr
      (fun y hy => (hasDerivAt_bellKernel hs0 hs1 hN0 hℓ0 hψ hy).deriv)
  have hae_half : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (1 / 2 : ℝ) := ae_ne_const _
  have hae_N : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (N : ℝ) := ae_ne_const _
  -- Pointwise bound on `(0, 1/2]`, where `min y (N - y) = y`.
  have hbd_left : ∀ y ∈ Ioo (0 : ℝ) (1 / 2),
      |bellKernel s N ℓ ψ y| ≤ C1 * bellConstant ℓ ψ * y ^ (-s) := by
    intro y hy
    have hmin : min y ((N : ℝ) - y) = y := min_eq_left (by linarith [hy.2])
    have h := hq y ⟨hy.1, by linarith [hy.2]⟩
    rwa [hmin] at h
  -- Pointwise bound on `(N - 1/2, N)`, by reflection onto `(0, 1/2)`.
  have hbd_right : ∀ y ∈ Ioo ((N : ℝ) - 1 / 2) N,
      |bellKernel s N ℓ ψ y| ≤ C1 * bellConstant ℓ ψ * ((N : ℝ) - y) ^ (-s) := by
    intro y hy
    have hy' : (N : ℝ) - y ∈ Ioo (0 : ℝ) N := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hmin : min ((N : ℝ) - y) ((N : ℝ) - ((N : ℝ) - y)) = (N : ℝ) - y := by
      rw [show (N : ℝ) - ((N : ℝ) - y) = y by ring]
      exact min_eq_left (by linarith [hy.1])
    have h := hq ((N : ℝ) - y) hy'
    rw [hmin, hr y ⟨by linarith [hy.1], hy.2⟩] at h
    exact h
  have hg_half : IntervalIntegrable (fun y : ℝ => C1 * bellConstant ℓ ψ * y ^ (-s)) volume 0 (1 / 2) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 / 2) (r := -s)
      (by linarith)).const_mul _
  have hint0 : IntervalIntegrable (bellKernel s N ℓ ψ) volume 0 (1 / 2) :=
    intervalIntegrable_of_bound (by norm_num)
      (hqc.mono (Ioo_subset_Ioo le_rfl (by linarith))) hg_half hbd_left hae_half
  have hint0abs : IntervalIntegrable (fun y => |bellKernel s N ℓ ψ y|) volume 0 (1 / 2) :=
    intervalIntegrable_of_bound (by norm_num)
      (continuous_abs.comp_continuousOn (hqc.mono (Ioo_subset_Ioo le_rfl (by linarith))))
      hg_half (fun y hy => by simp only [abs_abs]; exact hbd_left y hy) hae_half
  have hg_right : IntervalIntegrable
      (fun y : ℝ => C1 * bellConstant ℓ ψ * ((N : ℝ) - y) ^ (-s)) volume ((N : ℝ) - 1 / 2) N := by
    have h0 := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1 / 2) (r := -s)
      (by linarith)).comp_sub_left (N : ℝ)
    rw [sub_zero] at h0
    exact (intervalIntegrable_flip h0).const_mul _
  have hint_right : IntervalIntegrable (bellKernel s N ℓ ψ) volume ((N : ℝ) - 1 / 2) N :=
    intervalIntegrable_of_bound (by linarith)
      (hqc.mono (Ioo_subset_Ioo (by linarith) le_rfl)) hg_right hbd_right hae_N
  have hmain := bell_quadrature_sum_bound hN hqc hr hd hq'c hint0 hint_right
  -- The integral of `|q|` on `[0, 1/2]`.
  have hI0 : ∫ y in (0 : ℝ)..(1 / 2), |bellKernel s N ℓ ψ y|
      ≤ C1 * bellConstant ℓ ψ * ((1 / 2 : ℝ) ^ (1 - s) / (1 - s)) := by
    have hint_pow : ∫ y in (0 : ℝ)..(1 / 2), y ^ (-s) = (1 / 2 : ℝ) ^ (1 - s) / (1 - s) := by
      rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -s)),
        Real.zero_rpow (by intro h; linarith : (-s + 1 : ℝ) ≠ 0),
        show (-s + 1 : ℝ) = 1 - s by ring]
      ring
    calc ∫ y in (0 : ℝ)..(1 / 2), |bellKernel s N ℓ ψ y|
        ≤ ∫ y in (0 : ℝ)..(1 / 2), C1 * bellConstant ℓ ψ * y ^ (-s) :=
          intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hint0abs hg_half
            (fun y hy => hbd_left y hy)
      _ = C1 * bellConstant ℓ ψ * ∫ y in (0 : ℝ)..(1 / 2), y ^ (-s) :=
          intervalIntegral.integral_const_mul _ _
      _ = C1 * bellConstant ℓ ψ * ((1 / 2 : ℝ) ^ (1 - s) / (1 - s)) := by rw [hint_pow]
  -- The integral of `|q'|` on `[1/2, N - 1/2]`.
  have hJ : ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), |deriv (bellKernel s N ℓ ψ) y|
      ≤ C1 * bellConstant ℓ ψ * (2 * ((1 / 2 : ℝ) ^ (-s) / s)) := by
    have hsubN : Icc (1 / 2 : ℝ) ((N : ℝ) - 1 / 2) ⊆ Ioo 0 (N : ℝ) :=
      fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hc1 : ContinuousOn (fun y : ℝ => y ^ (-1 - s)) (Icc (1 / 2 : ℝ) ((N : ℝ) - 1 / 2)) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl (show (0 : ℝ) < x by linarith [hx.1]).ne')
    have hc2 : ContinuousOn (fun y : ℝ => ((N : ℝ) - y) ^ (-1 - s))
        (Icc (1 / 2 : ℝ) ((N : ℝ) - 1 / 2)) :=
      (continuous_const.sub continuous_id).continuousOn.rpow_const
        (fun x hx => Or.inl (show (0 : ℝ) < (N : ℝ) - x by linarith [hx.2]).ne')
    have hi1 : IntervalIntegrable (fun y : ℝ => y ^ (-1 - s)) volume (1 / 2) ((N : ℝ) - 1 / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc (by linarith) hc1
    have hi2 : IntervalIntegrable (fun y : ℝ => ((N : ℝ) - y) ^ (-1 - s)) volume
        (1 / 2) ((N : ℝ) - 1 / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc (by linarith) hc2
    have hdq_int : IntervalIntegrable (fun y => |deriv (bellKernel s N ℓ ψ) y|) volume
        (1 / 2) ((N : ℝ) - 1 / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc (by linarith)
        (continuous_abs.comp_continuousOn (hq'c.mono hsubN))
    have hpt : ∀ y ∈ Icc (1 / 2 : ℝ) ((N : ℝ) - 1 / 2),
        |deriv (bellKernel s N ℓ ψ) y|
          ≤ C1 * bellConstant ℓ ψ * (y ^ (-1 - s) + ((N : ℝ) - y) ^ (-1 - s)) := by
      intro y hy
      have h := hq' y (hsubN hy)
      have hm := rpow_min_le_add y ((N : ℝ) - y) (-1 - s) (by linarith [hy.1]) (by linarith [hy.2])
      calc |deriv (bellKernel s N ℓ ψ) y|
          ≤ C1 * bellConstant ℓ ψ * min y ((N : ℝ) - y) ^ (-1 - s) := h
        _ ≤ C1 * bellConstant ℓ ψ * (y ^ (-1 - s) + ((N : ℝ) - y) ^ (-1 - s)) :=
          mul_le_mul_of_nonneg_left hm hCA
    have hint_bound : ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), |deriv (bellKernel s N ℓ ψ) y|
        ≤ ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2),
            C1 * bellConstant ℓ ψ * (y ^ (-1 - s) + ((N : ℝ) - y) ^ (-1 - s)) :=
      intervalIntegral.integral_mono_on (by linarith) hdq_int ((hi1.add hi2).const_mul _) hpt
    -- Reflection of the second power onto the first.
    have hcomp : ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), ((N : ℝ) - y) ^ (-1 - s)
        = ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), y ^ (-1 - s) := by
      have h := intervalIntegral.integral_comp_sub_left (fun y : ℝ => y ^ (-1 - s)) (N : ℝ)
        (a := 1 / 2) (b := (N : ℝ) - 1 / 2)
      rw [show (N : ℝ) - ((N : ℝ) - 1 / 2) = 1 / 2 by ring] at h
      exact h
    -- The integral of `y^{-1-s}` on `[1/2, N - 1/2]`.
    have hpow_le : ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), y ^ (-1 - s) ≤ (1 / 2 : ℝ) ^ (-s) / s := by
      rw [integral_rpow (Or.inr ⟨by intro h; linarith,
        by rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1]⟩)]
      have e : (-1 - s + 1 : ℝ) = -s := by ring
      rw [e, div_neg, ← neg_div, neg_sub]
      refine div_le_div_of_nonneg_right ?_ hs0.le
      have hX : 0 ≤ ((N : ℝ) - 1 / 2) ^ (-s) := Real.rpow_nonneg (by linarith) _
      linarith
    calc ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), |deriv (bellKernel s N ℓ ψ) y|
        ≤ ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2),
            C1 * bellConstant ℓ ψ * (y ^ (-1 - s) + ((N : ℝ) - y) ^ (-1 - s)) := hint_bound
      _ = C1 * bellConstant ℓ ψ * ((∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), y ^ (-1 - s))
            + ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), ((N : ℝ) - y) ^ (-1 - s)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2]
      _ = C1 * bellConstant ℓ ψ * (2 * ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), y ^ (-1 - s)) := by
          rw [hcomp]
          ring
      _ ≤ C1 * bellConstant ℓ ψ * (2 * ((1 / 2 : ℝ) ^ (-s) / s)) :=
          mul_le_mul_of_nonneg_left (by linarith [hpow_le]) hCA
  have hsum_final : 2 * (∫ y in (0 : ℝ)..(1 / 2), |bellKernel s N ℓ ψ y|)
      + ∫ y in (1 / 2 : ℝ)..((N : ℝ) - 1 / 2), |deriv (bellKernel s N ℓ ψ) y|
      ≤ C1 * (2 * ((1 / 2 : ℝ) ^ (1 - s) / (1 - s)) + 2 * ((1 / 2 : ℝ) ^ (-s) / s))
          * bellConstant ℓ ψ := by
    have e : C1 * (2 * ((1 / 2 : ℝ) ^ (1 - s) / (1 - s)) + 2 * ((1 / 2 : ℝ) ^ (-s) / s))
        * bellConstant ℓ ψ
        = 2 * (C1 * bellConstant ℓ ψ * ((1 / 2 : ℝ) ^ (1 - s) / (1 - s)))
          + C1 * bellConstant ℓ ψ * (2 * ((1 / 2 : ℝ) ^ (-s) / s)) := by
      ring
    rw [e]
    linarith [hI0, hJ]
  exact ⟨hmain, hsum_final⟩

end Riesz1

end
