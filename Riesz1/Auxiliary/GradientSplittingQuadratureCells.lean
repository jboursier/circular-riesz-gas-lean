/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingCells
public import Riesz1.ToMathlib.UnitCellIntegral

/-!
# Cell estimates for the remainder of the reference field

The quadrature part of Lemma 5.7, full window. The remainder
`R_x` is smooth off the lattice `N ℤ`. This module gives the estimates on the unit
cells `[k - 1/2, k + 1/2]` that the quadrature needs:

* the integral of `|R_x'|` over the cell centred at `k`, with `1 ≤ |k| ≤ N/2`, is bounded by the
  weight of the cell part of Lemma 5.7 at `k`.
* the integral of `R_x` over a half cell differs from half the value at the centre by at most half
  the integral of `|R_x'|` over the cell.
* `R_x` is integrable on `[-N/2, N/2]`, and the integral over `[-N/2, N/2]` splits over the cells
  centred at `Ico (-m') (m'+1)` with `m' = (N-1)/2` and, for even `N`, the two half cells at the
  ends.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The remainder vanishes at the origin, by its definition `R_x(v) = -N^{-s}(v/N)^2 …`. -/
lemma gradCellR_zero (s : ℝ) (N : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ) (x : ℝ) :
    gradCellR s N ℓ ψ x 0 = 0 := by
  simp [gradCellR]

/-- The derivative of `R_x` is continuous on `gradCellSet N`, the open set of nonlattice points. -/
lemma continuousOn_deriv_gradCellR {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (x : ℝ) :
    ContinuousOn (deriv (gradCellR s N ℓ ψ x)) (gradCellSet N) :=
  ((contDiffOn_gradCellR hs0 hs1 hψ hℓ N x).deriv_of_isOpen (m := 0) (gradCellSet_isOpen N)
    (by simp)).continuousOn

/-- Points of the unit cell centred at an integer `k` with `1 ≤ |k| ≤ N/2` satisfy
`1/2 ≤ |v| ≤ 3N/4`, and they lie in `gradCellSet N`. -/
lemma mem_cell_bounds {N : ℕ} (hN : 2 ≤ N) {k : ℤ} (hk1 : 1 ≤ |(k : ℝ)|)
    (hkN : |(k : ℝ)| ≤ N / 2) {v : ℝ} (hv : v ∈ uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :
    v ∈ gradCellSet N ∧ 1 / 2 ≤ |v| ∧ |v| ≤ 3 * N / 4 := by
  have hle : (k : ℝ) - 1 / 2 ≤ (k : ℝ) + 1 / 2 := by linarith
  rw [uIcc_of_le hle, mem_Icc] at hv
  have hkv : |(k : ℝ) - v| ≤ 1 / 2 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hv.1, hv.2]
  have hv1 : 1 / 2 ≤ |v| := by
    have h := abs_sub_abs_le_abs_sub (k : ℝ) v
    linarith
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hv2 : |v| ≤ 3 * N / 4 := by
    have h := abs_add_le (k : ℝ) (v - (k : ℝ))
    rw [show (k : ℝ) + (v - (k : ℝ)) = v by ring, abs_sub_comm] at h
    linarith
  exact ⟨mem_gradCellSet_of_le hN (by linarith) hv2, hv1, hv2⟩

/-- For `1 ≤ |k|` and `|k|/2 ≤ |v|`, the power `|v|^{-1-s}` is at most `2^{1+s} |k|^{-1-s}`. -/
lemma rpow_abs_le_two_pow_mul {s : ℝ} (hs0 : 0 < s) {k v : ℝ} (hk : 1 ≤ |k|)
    (hv : |k| / 2 ≤ |v|) : |v| ^ (-1 - s) ≤ 2 ^ (1 + s) * |k| ^ (-1 - s) := by
  have hk0 : 0 < |k| / 2 := by linarith
  have h1 : |v| ^ (-1 - s) ≤ (|k| / 2) ^ (-1 - s) :=
    Real.rpow_le_rpow_of_nonpos hk0 hv (by linarith)
  have h2' : (2 : ℝ) ^ (-1 - s) = ((2 : ℝ) ^ (1 + s))⁻¹ := by
    rw [show (-1 - s) = -(1 + s) by ring, Real.rpow_neg (by norm_num)]
  have h2 : (|k| / 2) ^ (-1 - s) = 2 ^ (1 + s) * |k| ^ (-1 - s) := by
    rw [Real.div_rpow (abs_nonneg k) (by norm_num), h2', div_inv_eq_mul]
    ring
  linarith

/-- The integral of `|R_x'|` over the unit cell centred at `k`, `1 ≤ |k| ≤ N/2`, is bounded by the
weight of the cell part of Lemma 5.7 at `k`: the weight `|v|^{-1-s}` is compared with its value
at the centre `|k|^{-1-s}`, and the weight `w_2` with its value at `(x + k/N)/ℓ` (the shift is at most
half a microscopic cell). -/
theorem cell_abs_deriv_integral_le {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α)
    (hα1 : α < s / 2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (N : ℕ) (ℓ C0 x : ℝ) (ψ : ℝ → ℝ) (k : ℤ),
      2 ≤ N → 0 < ℓ → ℓ ≤ 1 → 1 ≤ N * ℓ → 0 ≤ C0 → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) (N * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ t) →
      1 ≤ |(k : ℝ)| → |(k : ℝ)| ≤ N / 2 →
      ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s N ℓ ψ x) v|
        ≤ C₁ * C0 * ℓ⁻¹ * (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ)
          + gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + k / N) / ℓ)) * |(k : ℝ)| ^ (-1 - s) := by
  obtain ⟨C, hC, hcells⟩ := gradient_splitting_cells hs0 hs1 hα0 hα1
  refine ⟨C * (64 * 2 ^ (1 - s + α)) * 2 ^ (1 + s), by positivity, ?_⟩
  intro N ℓ C0 x ψ k hN hℓ hℓ1 hK hC0 hψ hper h1 h2 hk1 hkN
  have hcell := (hcells N ℓ C0 x ψ hN hℓ hℓ1 hK hC0 hψ hper h1 h2).2.2.1
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNℓ : 0 < (N : ℝ) * ℓ := by positivity
  have ha0 : (0 : ℝ) ≤ 1 - s + α := by linarith
  have hk0 : (0 : ℝ) < |(k : ℝ)| := by linarith
  have hle : (k : ℝ) - 1 / 2 ≤ (k : ℝ) + 1 / 2 := by linarith
  have hA0 : 0 ≤ gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) :=
    gradCell_w2_nonneg _ _ _ _ _
  have hB0 : 0 ≤ gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + k / N) / ℓ) :=
    gradCell_w2_nonneg _ _ _ _ _
  have h64 : (1 : ℝ) ≤ 64 * 2 ^ (1 - s + α) := by
    have : (1 : ℝ) ≤ 2 ^ (1 - s + α) := Real.one_le_rpow (by norm_num) ha0
    linarith
  set A := gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) with hAdef
  set B := gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + k / N) / ℓ) with hBdef
  have hpt : ∀ v ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
      |deriv (gradCellR s N ℓ ψ x) v| ≤
        C * (64 * 2 ^ (1 - s + α)) * 2 ^ (1 + s) * C0 * ℓ⁻¹ * (A + B) * |(k : ℝ)| ^ (-1 - s) := by
    intro v hv
    have hvU : v ∈ uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := by
      rw [uIcc_of_le hle]
      exact hv
    obtain ⟨_, hv1, hv2⟩ := mem_cell_bounds hN hk1 hkN hvU
    have hbound := hcell v hv1 hv2
    have hvk : |v - (k : ℝ)| ≤ 1 / 2 := by
      rw [uIcc_of_le hle, mem_Icc] at hvU
      rw [abs_le]
      constructor <;> linarith [hvU.1, hvU.2]
    have hδ : |(v - (k : ℝ)) / ((N : ℝ) * ℓ)| ≤ 1 / (2 * ((N : ℝ) * ℓ)) := by
      rw [abs_div, abs_of_pos hNℓ]
      calc |v - (k : ℝ)| / ((N : ℝ) * ℓ) ≤ (1 / 2) / ((N : ℝ) * ℓ) :=
            div_le_div_of_nonneg_right hvk hNℓ.le
        _ = 1 / (2 * ((N : ℝ) * ℓ)) := by ring
    have hshift := gradCell_w2_shift (u := (x + (k : ℝ) / N) / ℓ) hs0 hs1 ha0 hK
      (inv_pos.mpr hℓ) hδ
    have heq : (x + v / N) / ℓ = (x + k / N) / ℓ + (v - (k : ℝ)) / ((N : ℝ) * ℓ) := by
      field_simp
      ring
    rw [← heq] at hshift
    have hAB : A + gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)
        ≤ 64 * 2 ^ (1 - s + α) * (A + B) := by
      nlinarith
    have hpow := rpow_abs_le_two_pow_mul hs0 hk1 (show |(k : ℝ)| / 2 ≤ |v| by
      have hh := abs_sub_abs_le_abs_sub (k : ℝ) v
      have hh' : |(k : ℝ) - v| = |v - (k : ℝ)| := abs_sub_comm _ _
      linarith)
    have hC0ℓ : 0 ≤ C * C0 * ℓ⁻¹ := by
      have : 0 ≤ C := hC.le
      positivity
    calc |deriv (gradCellR s N ℓ ψ x) v|
        ≤ C * C0 * ℓ⁻¹ * (A + gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))
          * |v| ^ (-1 - s) := hbound
      _ ≤ C * C0 * ℓ⁻¹ * (64 * 2 ^ (1 - s + α) * (A + B)) * (2 ^ (1 + s) * |(k : ℝ)| ^ (-1 - s)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hAB hC0ℓ) hpow
          · exact Real.rpow_nonneg (abs_nonneg _) _
          · have := mul_nonneg (by positivity : (0 : ℝ) ≤ 64 * 2 ^ (1 - s + α))
              (add_nonneg hA0 hB0)
            exact mul_nonneg hC0ℓ this
      _ = C * (64 * 2 ^ (1 - s + α)) * 2 ^ (1 + s) * C0 * ℓ⁻¹ * (A + B) * |(k : ℝ)| ^ (-1 - s) := by
          ring
  have hcont : ContinuousOn (fun v => |deriv (gradCellR s N ℓ ψ x) v|)
      (uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) := by
    apply ContinuousOn.abs
    refine (continuousOn_deriv_gradCellR hs0 hs1 hψ hℓ N x).mono ?_
    intro v hv
    exact (mem_cell_bounds hN hk1 hkN hv).1
  calc ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s N ℓ ψ x) v|
      ≤ ∫ _ in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
          C * (64 * 2 ^ (1 - s + α)) * 2 ^ (1 + s) * C0 * ℓ⁻¹ * (A + B) * |(k : ℝ)| ^ (-1 - s) :=
        intervalIntegral.integral_mono_on hle hcont.intervalIntegrable
          intervalIntegrable_const hpt
    _ = C * (64 * 2 ^ (1 - s + α)) * 2 ^ (1 + s) * C0 * ℓ⁻¹ * (A + B) * |(k : ℝ)| ^ (-1 - s) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- Two points of a unit cell `[p, q]` on which `R_x` is smooth: the difference of the values of
`R_x` is at most the integral of `|R_x'|` over the cell. -/
lemma abs_gradCellR_sub_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (x : ℝ) {p q : ℝ} (hpq : p ≤ q)
    (hcell : ∀ v ∈ uIcc p q, v ∈ gradCellSet N) {u v : ℝ} (hu : u ∈ uIcc p q)
    (hv : v ∈ uIcc p q) :
    |gradCellR s N ℓ ψ x v - gradCellR s N ℓ ψ x u|
      ≤ ∫ t in p..q, |deriv (gradCellR s N ℓ ψ x) t| := by
  have hcont : ContinuousOn (deriv (gradCellR s N ℓ ψ x)) (uIcc p q) :=
    (continuousOn_deriv_gradCellR hs0 hs1 hψ hℓ N x).mono hcell
  have hderiv : ∀ t ∈ uIcc p q, HasDerivAt (gradCellR s N ℓ ψ x) (deriv (gradCellR s N ℓ ψ x) t) t := by
    intro t ht
    have hdiff := ((contDiffOn_gradCellR hs0 hs1 hψ hℓ N x).differentiableOn (by simp)).differentiableAt
      ((gradCellSet_isOpen N).mem_nhds (hcell t ht))
    exact hdiff.hasDerivAt
  have hint : IntervalIntegrable (fun t => |deriv (gradCellR s N ℓ ψ x) t|) volume p q :=
    hcont.intervalIntegrable.abs
  have hnn : ∀ a b : ℝ, a ∈ uIcc p q → b ∈ uIcc p q → a ≤ b →
      |∫ t in a..b, deriv (gradCellR s N ℓ ψ x) t| ≤ ∫ t in p..q, |deriv (gradCellR s N ℓ ψ x) t| := by
    intro a b ha hb hab
    rw [uIcc_of_le hpq] at ha hb
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc p q)] fun t => |deriv (gradCellR s N ℓ ψ x) t| :=
      Filter.Eventually.of_forall fun t => abs_nonneg _
    calc |∫ t in a..b, deriv (gradCellR s N ℓ ψ x) t|
        ≤ ∫ t in a..b, |deriv (gradCellR s N ℓ ψ x) t| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in p..q, |deriv (gradCellR s N ℓ ψ x) t| :=
          intervalIntegral.integral_mono_interval ha.1 hab hb.2 hnonneg hint
  have hsub : ∀ a b : ℝ, a ∈ uIcc p q → b ∈ uIcc p q →
      gradCellR s N ℓ ψ x b - gradCellR s N ℓ ψ x a
        = ∫ t in a..b, deriv (gradCellR s N ℓ ψ x) t := by
    intro a b ha hb
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_).symm
    · intro t ht
      exact hderiv t (uIcc_subset_uIcc ha hb ht)
    · exact hcont.mono (uIcc_subset_uIcc ha hb) |>.intervalIntegrable
  rw [hsub u v hu hv]
  rcases le_total u v with huv | huv
  · exact hnn u v hu hv huv
  · rw [intervalIntegral.integral_symm, abs_neg]
    exact hnn v u hv hu huv

/-- The integral of `R_x` over an interval `[a, b]` differs from `(b - a) R_x(c)` by at most
`I |b - a|`, when `|R_x(v) - R_x(c)| ≤ I` on `[a, b]`. -/
lemma abs_integral_sub_mul_le {R : ℝ → ℝ} {a b c I : ℝ} (hR : IntervalIntegrable R volume a b)
    (hI : ∀ v ∈ uIcc a b, |R v - R c| ≤ I) :
    |(∫ v in a..b, R v) - (b - a) * R c| ≤ I * |b - a| := by
  have heq : (∫ v in a..b, R v) - (b - a) * R c = ∫ v in a..b, (R v - R c) := by
    rw [intervalIntegral.integral_sub hR intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
  rw [heq]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun v => R v - R c) (C := I) (fun v hv => by
      rw [Real.norm_eq_abs]
      exact hI v (Set.uIoc_subset_uIcc hv))
  rwa [Real.norm_eq_abs] at hnorm

/-- Half cells: the integral of `R_x` over `[c - 1/2, c]` or over `[c, c + 1/2]` differs from
half the value `R_x(c)` by at most half the integral of `|R_x'|` over the cell `[c - 1/2, c + 1/2]`. -/
lemma gradCellR_half_cell_avg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (x : ℝ) {c : ℝ}
    (hcell : ∀ v ∈ uIcc (c - 1 / 2) (c + 1 / 2), v ∈ gradCellSet N) :
    |(∫ v in (c - 1 / 2)..c, gradCellR s N ℓ ψ x v) - gradCellR s N ℓ ψ x c / 2|
        ≤ 1 / 2 * ∫ t in (c - 1 / 2)..(c + 1 / 2), |deriv (gradCellR s N ℓ ψ x) t| ∧
      |(∫ v in c..(c + 1 / 2), gradCellR s N ℓ ψ x v) - gradCellR s N ℓ ψ x c / 2|
        ≤ 1 / 2 * ∫ t in (c - 1 / 2)..(c + 1 / 2), |deriv (gradCellR s N ℓ ψ x) t| := by
  have hc1 : c - 1 / 2 ≤ c + 1 / 2 := by linarith
  have hcU : c ∈ uIcc (c - 1 / 2) (c + 1 / 2) := by
    rw [uIcc_of_le hc1]
    constructor <;> linarith
  have hcont : ContinuousOn (gradCellR s N ℓ ψ x) (uIcc (c - 1 / 2) (c + 1 / 2)) :=
    ((contDiffOn_gradCellR hs0 hs1 hψ hℓ N x).continuousOn).mono hcell
  have hI : ∀ v ∈ uIcc (c - 1 / 2) (c + 1 / 2),
      |gradCellR s N ℓ ψ x v - gradCellR s N ℓ ψ x c| ≤
        ∫ t in (c - 1 / 2)..(c + 1 / 2), |deriv (gradCellR s N ℓ ψ x) t| :=
    fun v hv => abs_gradCellR_sub_le hs0 hs1 hψ hℓ x hc1 hcell hcU hv
  have hsub1 : uIcc (c - 1 / 2) c ⊆ uIcc (c - 1 / 2) (c + 1 / 2) :=
    uIcc_subset_uIcc (left_mem_uIcc) (by rw [uIcc_of_le hc1]; constructor <;> linarith)
  have hsub2 : uIcc c (c + 1 / 2) ⊆ uIcc (c - 1 / 2) (c + 1 / 2) :=
    uIcc_subset_uIcc (by rw [uIcc_of_le hc1]; constructor <;> linarith) right_mem_uIcc
  have hR1 : IntervalIntegrable (gradCellR s N ℓ ψ x) volume (c - 1 / 2) c :=
    (hcont.mono hsub1).intervalIntegrable
  have hR2 : IntervalIntegrable (gradCellR s N ℓ ψ x) volume c (c + 1 / 2) :=
    (hcont.mono hsub2).intervalIntegrable
  have hb1 := abs_integral_sub_mul_le hR1 (c := c)
    (I := ∫ t in (c - 1 / 2)..(c + 1 / 2), |deriv (gradCellR s N ℓ ψ x) t|)
    (fun v hv => hI v (hsub1 hv))
  have hb2 := abs_integral_sub_mul_le hR2 (c := c)
    (I := ∫ t in (c - 1 / 2)..(c + 1 / 2), |deriv (gradCellR s N ℓ ψ x) t|)
    (fun v hv => hI v (hsub2 hv))
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  constructor
  · rw [show c - (c - 1 / 2) = 1 / 2 by ring, abs_of_pos hhalf] at hb1
    rw [show gradCellR s N ℓ ψ x c / 2 = 1 / 2 * gradCellR s N ℓ ψ x c by ring]
    linarith
  · rw [show c + 1 / 2 - c = 1 / 2 by ring, abs_of_pos hhalf] at hb2
    rw [show gradCellR s N ℓ ψ x c / 2 = 1 / 2 * gradCellR s N ℓ ψ x c by ring]
    linarith

/-- A point with `1/2 ≤ |v| ≤ N/2` lies in `gradCellSet N`. -/
lemma mem_gradCellSet_of_half_le {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (h1 : 1 / 2 ≤ |v|)
    (h2 : |v| ≤ N / 2) : v ∈ gradCellSet N :=
  mem_gradCellSet_of_le hN (by linarith) (by
    have hN' : (0 : ℝ) ≤ N := by positivity
    linarith)

/-- The value of the kernel `h = gradKernelH s` at `1/2` vanishes, since `ψ` has no derivative of
the kernel at the half period. -/
lemma gradKernelH_half (s : ℝ) : gradKernelH s (1 / 2) = 0 := by
  unfold gradKernelH
  rw [gradSplit_deriv_kernel_half, mul_zero]

/-- The reference increment `F_x` takes the same value at `N/2` and `-N/2`. It uses
the periodicity `ψ(t - 1/ℓ) = ψ(t)` and the vanishing of the kernel `h` at `±1/2`. -/
lemma gradCellF_antipode_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hper : Function.Periodic ψ ℓ⁻¹) {N : ℕ}
    (hN : 2 ≤ N) (x : ℝ) :
    gradCellF s N ℓ ψ x ((N : ℝ) / 2) = gradCellF s N ℓ ψ x (-((N : ℝ) / 2)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hdiv1 : ((N : ℝ) / 2) / (N : ℝ) = 1 / 2 := by
    field_simp
  have hdiv2 : (-((N : ℝ) / 2)) / (N : ℝ) = -(1 / 2) := by
    field_simp
  have hz : gradZ ψ ℓ x (x + -(1 / 2)) = -gradZ ψ ℓ x (x + 1 / 2) := by
    have hne1 : x + 1 / 2 ≠ x := by intro h; linarith
    have hne2 : x + -(1 / 2) ≠ x := by intro h; linarith
    rw [gradZ_eq_quot hψ hℓ hne1, gradZ_eq_quot hψ hℓ hne2]
    have hper' : ψ ((x + -(1 / 2)) / ℓ) = ψ ((x + 1 / 2) / ℓ) := by
      rw [show (x + -(1 / 2)) / ℓ = (x + 1 / 2) / ℓ - ℓ⁻¹ by ring, hper.sub_eq]
    rw [hper']
    field_simp
    ring
  have hh' : iteratedDeriv 1 (gradKernelH s) (-(1 / 2)) = -iteratedDeriv 1 (gradKernelH s) (1 / 2) :=
    gradSplit_iteratedDeriv_one_gradKernelH_neg s hs0 hs1
      (gradSplit_coe_ne_zero (by norm_num) (by norm_num))
  have hevenH : gradKernelH s (-(1 / 2)) = 0 := by
    rw [gradSplit_gradKernelH_even, gradKernelH_half]
  unfold gradCellF
  rw [hdiv1, hdiv2, gradKernelH_half, hevenH, hh', hz]
  ring

/-- At the antipodes `σ = ±N/2`, the remainder `R_x(σ)` differs from the average of `R_x(±N/2)` by
`N^{-s} |ψ'(x/ℓ)| |h'(1/2)|`: the two values of `R_x` at the antipodes differ by the odd part of
`F_x` at them. -/
lemma gradCellR_antipode_avg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hper : Function.Periodic ψ ℓ⁻¹) {N : ℕ}
    (hN : 2 ≤ N) (x : ℝ) {σ : ℝ} (hσ : σ = (N : ℝ) / 2 ∨ σ = -((N : ℝ) / 2)) :
    |gradCellR s N ℓ ψ x σ
        - (gradCellR s N ℓ ψ x ((N : ℝ) / 2) + gradCellR s N ℓ ψ x (-((N : ℝ) / 2))) / 2|
      = (N : ℝ) ^ (-s) * |deriv ψ (x / ℓ)| * |iteratedDeriv 1 (gradKernelH s) (1 / 2)| := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hm1 : (N : ℝ) / 2 ∈ gradCellSet N :=
    mem_gradCellSet_of_half_le hN (by rw [abs_of_pos (by linarith)]; linarith)
      (by rw [abs_of_pos (by linarith)])
  have hm2 : -((N : ℝ) / 2) ∈ gradCellSet N :=
    mem_gradCellSet_of_half_le hN (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
      (by rw [abs_neg, abs_of_pos (by linarith)])
  have hdiv1 : ((N : ℝ) / 2) / (N : ℝ) = 1 / 2 := by
    field_simp
  have hdiv2 : (-((N : ℝ) / 2)) / (N : ℝ) = -(1 / 2) := by
    field_simp
  have hF1 := gradCellF_eq (ψ := ψ) (ℓ := ℓ) hs0 hs1 N x hm1
  have hF2 := gradCellF_eq (ψ := ψ) (ℓ := ℓ) hs0 hs1 N x hm2
  rw [hdiv1] at hF1
  rw [hdiv2] at hF2
  have hh' : iteratedDeriv 1 (gradKernelH s) (-(1 / 2))
      = -iteratedDeriv 1 (gradKernelH s) (1 / 2) :=
    gradSplit_iteratedDeriv_one_gradKernelH_neg s hs0 hs1
      (gradSplit_coe_ne_zero (by norm_num) (by norm_num))
  rw [hh'] at hF2
  have hFeq := gradCellF_antipode_eq hs0 hs1 hψ hℓ hper hN x
  have hA : 0 ≤ (N : ℝ) ^ (-s) := Real.rpow_nonneg hNpos.le _
  rcases hσ with rfl | rfl
  · have key : gradCellR s N ℓ ψ x ((N : ℝ) / 2)
        - (gradCellR s N ℓ ψ x ((N : ℝ) / 2) + gradCellR s N ℓ ψ x (-((N : ℝ) / 2))) / 2
        = (N : ℝ) ^ (-s) * deriv ψ (x / ℓ) * iteratedDeriv 1 (gradKernelH s) (1 / 2) := by
      linarith
    rw [key, abs_mul, abs_mul, abs_of_nonneg hA]
  · have key : gradCellR s N ℓ ψ x (-((N : ℝ) / 2))
        - (gradCellR s N ℓ ψ x ((N : ℝ) / 2) + gradCellR s N ℓ ψ x (-((N : ℝ) / 2))) / 2
        = -((N : ℝ) ^ (-s) * deriv ψ (x / ℓ) * iteratedDeriv 1 (gradKernelH s) (1 / 2)) := by
      linarith
    rw [key, abs_neg, abs_mul, abs_mul, abs_of_nonneg hA]

/-- The remainder is integrable on `[-N/2, N/2]`: it is continuous off `0`, and integrable on the
central cell by the cell part of Lemma 5.7. -/
theorem intervalIntegrable_gradCellR_half {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) {N : ℕ} {ℓ C0 x : ℝ} {ψ : ℝ → ℝ} (hN : 2 ≤ N)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 1 ≤ (N : ℝ) * ℓ) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹)
    (h1 : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t)
    (h2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) :
    IntervalIntegrable (gradCellR s N ℓ ψ x) volume (-((N : ℝ) / 2)) ((N : ℝ) / 2) := by
  obtain ⟨C, hC, hcells⟩ := gradient_splitting_cells hs0 hs1 hα0 hα1
  have hmid := (hcells N ℓ C0 x ψ hN hℓ hℓ1 hK hC0 hψ hper h1 h2).2.2.2.1
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcont : ∀ p q : ℝ, (∀ v ∈ uIcc p q, v ∈ gradCellSet N) →
      IntervalIntegrable (gradCellR s N ℓ ψ x) volume p q := fun p q hc =>
    (((contDiffOn_gradCellR hs0 hs1 hψ hℓ N x).continuousOn).mono hc).intervalIntegrable
  have hright : IntervalIntegrable (gradCellR s N ℓ ψ x) volume (1 / 2) ((N : ℝ) / 2) := by
    refine hcont _ _ (fun v hv => ?_)
    rw [uIcc_of_le (by linarith)] at hv
    apply mem_gradCellSet_of_half_le hN
    · rw [abs_of_pos (by linarith [hv.1])]
      exact hv.1
    · rw [abs_of_pos (by linarith [hv.1])]
      exact hv.2
  have hleft : IntervalIntegrable (gradCellR s N ℓ ψ x) volume (-((N : ℝ) / 2)) (-(1 / 2)) := by
    refine hcont _ _ (fun v hv => ?_)
    rw [uIcc_of_le (by linarith)] at hv
    apply mem_gradCellSet_of_half_le hN
    · rw [abs_of_neg (by linarith [hv.2])]
      linarith [hv.2]
    · rw [abs_of_neg (by linarith [hv.2])]
      linarith [hv.1]
  exact (hleft.trans hmid).trans hright

/-- Restriction of interval integrability to a subinterval. -/
lemma intervalIntegrable_of_le_of_le {f : ℝ → ℝ} {p q p' q' : ℝ} (hpq : p ≤ q)
    (hf : IntervalIntegrable f volume p q) (h1 : p ≤ p') (h2 : p' ≤ q') (h3 : q' ≤ q) :
    IntervalIntegrable f volume p' q' := by
  refine hf.mono_set ?_
  rw [uIcc_of_le hpq, uIcc_of_le (by linarith)]
  exact Set.Icc_subset_Icc h1 h3

/-- The integral of `R_x` over `[-N/2, N/2]` splits over the unit cells centred at the integers
`-m' ≤ k ≤ m'`, with `N = 2m'+1` (odd `N`) or `N = 2m'+2` (even `N`). For even `N` the remaining
two half cells at the ends are added. -/
theorem integral_gradCellR_split (s : ℝ) {N : ℕ} (hN : 2 ≤ N) (ℓ : ℝ) (ψ : ℝ → ℝ) (x : ℝ)
    (m' : ℤ) (hm : (N : ℤ) = 2 * m' + 1 ∨ (N : ℤ) = 2 * m' + 2)
    (hint : IntervalIntegrable (gradCellR s N ℓ ψ x) volume (-((N : ℝ) / 2)) ((N : ℝ) / 2)) :
    (∫ v in (-((N : ℝ) / 2))..((N : ℝ) / 2), gradCellR s N ℓ ψ x v)
      = ∑ k ∈ Finset.Ico (-m') (m' + 1), (∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
            gradCellR s N ℓ ψ x v)
        + (if (N : ℕ) % 2 = 0 then
            (∫ v in (-((N : ℝ) / 2))..(-((N : ℝ) / 2) + 1 / 2), gradCellR s N ℓ ψ x v)
              + (∫ v in ((N : ℝ) / 2 - 1 / 2)..((N : ℝ) / 2), gradCellR s N ℓ ψ x v)
          else 0) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : 0 ≤ m' := by omega
  have hm0R : (0 : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hm0
  have hpq : -((N : ℝ) / 2) ≤ (N : ℝ) / 2 := by linarith
  by_cases heven : (N : ℕ) % 2 = 0
  · have hNe : (N : ℤ) = 2 * m' + 2 := by omega
    have hNe' : (N : ℝ) = 2 * (m' : ℝ) + 2 := by exact_mod_cast hNe
    have e1 : ((-m' : ℤ) : ℝ) - 1 / 2 = -((N : ℝ) / 2) + 1 / 2 := by
      push_cast
      rw [hNe']
      ring
    have e2 : ((m' + 1 : ℤ) : ℝ) - 1 / 2 = (N : ℝ) / 2 - 1 / 2 := by
      push_cast
      rw [hNe']
      ring
    have hmid : IntervalIntegrable (gradCellR s N ℓ ψ x) volume
        (-((N : ℝ) / 2) + 1 / 2) ((N : ℝ) / 2 - 1 / 2) :=
      intervalIntegrable_of_le_of_le hpq hint (by linarith) (by linarith) (by linarith)
    have htile := sum_Ico_unitCell_integral (f := gradCellR s N ℓ ψ x) (a := -m') (b := m' + 1)
      (by omega) (by rw [e1, e2]; exact hmid)
    rw [e1, e2] at htile
    have hlow : IntervalIntegrable (gradCellR s N ℓ ψ x) volume
        (-((N : ℝ) / 2)) (-((N : ℝ) / 2) + 1 / 2) :=
      intervalIntegrable_of_le_of_le hpq hint le_rfl (by linarith) (by linarith)
    have hhigh : IntervalIntegrable (gradCellR s N ℓ ψ x) volume
        ((N : ℝ) / 2 - 1 / 2) ((N : ℝ) / 2) :=
      intervalIntegrable_of_le_of_le hpq hint (by linarith) (by linarith) le_rfl
    have hA := intervalIntegral.integral_add_adjacent_intervals hlow
      (hmid.trans hhigh)
    have hB := intervalIntegral.integral_add_adjacent_intervals hmid hhigh
    simp only [heven, ↓reduceIte]
    rw [← hA, ← hB, htile]
    ring
  · have hNo : (N : ℤ) = 2 * m' + 1 := by omega
    have hNo' : (N : ℝ) = 2 * (m' : ℝ) + 1 := by exact_mod_cast hNo
    have e1 : ((-m' : ℤ) : ℝ) - 1 / 2 = -((N : ℝ) / 2) := by
      push_cast
      rw [hNo']
      ring
    have e2 : ((m' + 1 : ℤ) : ℝ) - 1 / 2 = (N : ℝ) / 2 := by
      push_cast
      rw [hNo']
      ring
    have htile := sum_Ico_unitCell_integral (f := gradCellR s N ℓ ψ x) (a := -m') (b := m' + 1)
      (by omega) (by rw [e1, e2]; exact hint)
    rw [e1, e2] at htile
    simp only [heven, ↓reduceIte, add_zero]
    rw [htile]

end

end Riesz1
