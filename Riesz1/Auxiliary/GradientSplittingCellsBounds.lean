/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingCellsDeriv

/-!
# Bounds on the remainder of the one-cell quadrature

The cell part of Lemma 5.7: the pointwise bound on `R_x`,
its local integrability at zero, and the bound `∫_{-1/2}^{1/2} |R_x| ≤ C C_0 ℓ^{-1} w_2(x/ℓ)`.

The weight `w_2` moves by at most the factor `64 · 2^a` under a shift of size `1/(2K)`, where
`K = Nℓ` (`gradCell_w2_shift`). This is the comparison that makes the bound a multiple of the value
at `x/ℓ` alone. The two ratio lemmas are copies of `gradWeightTwo_half_le` and
`gradWeightTwo_ratio` of `GradientSplittingConvolutionLattice.lean`. That file cannot be imported
together with the differences chain, since both declare `Riesz1.gradWeightOne_nonneg`.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-! ### Comparison of the weight `w_2` under a shift -/

/-- The comparison `w_2(t/2) ≤ 64 · 2^a · w_2(t)` at the level of the distance function. A copy of
`gradWeightTwo_half_le` of `GradientSplittingConvolutionLattice.lean`. -/
lemma gradCell_w2_half_le {s a K : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K)
    {t : ℝ} :
    (if t / 2 < 1 then max (t / 2) K⁻¹ ^ (-(1 + a)) else (t / 2) ^ (s - 3)) ≤
      64 * 2 ^ a * (if t < 1 then max t K⁻¹ ^ (-(1 + a)) else t ^ (s - 3)) := by
  have hK0 : 0 < K⁻¹ := inv_pos.mpr (by linarith)
  have h2a : 1 ≤ (2 : ℝ) ^ a := Real.one_le_rpow (by norm_num) ha
  have hpow1 : (2 : ℝ) ^ (1 + a) = 2 * 2 ^ a := by
    rw [Real.rpow_add (show (0 : ℝ) < 2 by norm_num), Real.rpow_one]
  have hpow3 : (1 / 8 : ℝ) ≤ (2 : ℝ) ^ (s - 3) := by
    have h1 : (2 : ℝ) ^ (-3 : ℝ) ≤ (2 : ℝ) ^ (s - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by
      rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num)]
      norm_num
    rw [← h2]
    exact h1
  by_cases ht1 : t < 1
  · rw [ite_eq_left (show t / 2 < 1 by linarith), ite_eq_left ht1]
    have hx0 : 0 < max t K⁻¹ := lt_of_lt_of_le hK0 (le_max_right _ _)
    have hhalf : max t K⁻¹ / 2 ≤ max (t / 2) K⁻¹ := by
      rcases le_total t K⁻¹ with h | h
      · rw [max_eq_right h]
        have := le_max_right (t / 2) K⁻¹
        linarith
      · rw [max_eq_left h]
        have := le_max_left (t / 2) K⁻¹
        linarith
    have hmono : max (t / 2) K⁻¹ ^ (-(1 + a)) ≤ (max t K⁻¹ / 2) ^ (-(1 + a)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
    have hdiv : (max t K⁻¹ / 2) ^ (-(1 + a)) = 2 * 2 ^ a * (max t K⁻¹) ^ (-(1 + a)) := by
      rw [Real.div_rpow hx0.le (show (0 : ℝ) ≤ 2 by norm_num),
        Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) (1 + a), div_inv_eq_mul, hpow1]
      ring
    have hnonneg : 0 ≤ (max t K⁻¹) ^ (-(1 + a)) := Real.rpow_nonneg hx0.le _
    calc max (t / 2) K⁻¹ ^ (-(1 + a)) ≤ (max t K⁻¹ / 2) ^ (-(1 + a)) := hmono
      _ = 2 * 2 ^ a * (max t K⁻¹) ^ (-(1 + a)) := hdiv
      _ ≤ 64 * 2 ^ a * (max t K⁻¹) ^ (-(1 + a)) := by
          apply mul_le_mul_of_nonneg_right _ hnonneg
          nlinarith
  · rw [ite_eq_right ht1]
    have ht1' : 1 ≤ t := not_lt.mp ht1
    by_cases ht2 : t < 2
    · rw [ite_eq_left (show t / 2 < 1 by linarith)]
      have hge : (1 / 2 : ℝ) ≤ max (t / 2) K⁻¹ := le_trans (by linarith) (le_max_left _ _)
      have hLHS : max (t / 2) K⁻¹ ^ (-(1 + a)) ≤ (1 / 2 : ℝ) ^ (-(1 + a)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hge (by linarith)
      have hval : (1 / 2 : ℝ) ^ (-(1 + a)) = 2 * 2 ^ a := by
        rw [one_div, Real.inv_rpow (show (0 : ℝ) ≤ 2 by norm_num),
          Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num), inv_inv, hpow1]
      have hRHS : (1 / 8 : ℝ) ≤ t ^ (s - 3) := by
        have h1 : (2 : ℝ) ^ (s - 3) ≤ t ^ (s - 3) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) ht2.le (by linarith)
        linarith
      calc max (t / 2) K⁻¹ ^ (-(1 + a)) ≤ 2 * 2 ^ a := hLHS.trans hval.le
        _ ≤ 64 * 2 ^ a * (1 / 8) := by linarith
        _ ≤ 64 * 2 ^ a * t ^ (s - 3) := mul_le_mul_of_nonneg_left hRHS (by positivity)
    · rw [ite_eq_right (not_lt.mpr (show 1 ≤ t / 2 by linarith))]
      have ht0 : 0 ≤ t := by linarith
      rw [Real.div_rpow ht0 (show (0 : ℝ) ≤ 2 by norm_num)]
      have htpos : 0 ≤ t ^ (s - 3) := Real.rpow_nonneg ht0 _
      have h2pos : 0 < (2 : ℝ) ^ (s - 3) := by positivity
      rw [div_le_iff₀ h2pos]
      have hc : 1 ≤ 64 * 2 ^ a * (2 : ℝ) ^ (s - 3) := by
        have hm := mul_le_mul h2a hpow3 (by norm_num) (by positivity)
        nlinarith
      nlinarith [mul_nonneg htpos (sub_nonneg.mpr hc)]

/-- The ratio bound `w_2(v) ≤ 64 · 2^a · w_2(u)` when `circDist u = t` and `circDist v = t/2`. A
copy of `gradWeightTwo_ratio` of `GradientSplittingConvolutionLattice.lean`. -/
lemma gradCell_w2_ratio {s a K L t u v : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K)
    (hu : circDist L u = t) (hv : circDist L v = t / 2) :
    gradWeightTwo s a K L v ≤ 64 * 2 ^ a * gradWeightTwo s a K L u := by
  unfold gradWeightTwo
  rw [hu, hv]
  exact gradCell_w2_half_le hs0 hs1 ha hK

/-- The weight `w_2` is nonnegative. -/
lemma gradCell_w2_nonneg (s a K L u : ℝ) : 0 ≤ gradWeightTwo s a K L u := by
  unfold gradWeightTwo
  split_ifs
  · exact Real.rpow_nonneg (le_max_of_le_left (abs_nonneg _)) _
  · exact Real.rpow_nonneg (abs_nonneg _) _

/-- The circular distance is nonnegative. -/
lemma gradCell_circDist_nonneg (L u : ℝ) : 0 ≤ circDist L u := abs_nonneg _

/-- Shifting a point by `δ` changes its circular distance by at most `|δ|`. -/
lemma gradCell_circDist_add_le {L : ℝ} (hL : 0 < L) (u δ : ℝ) :
    circDist L (u + δ) ≤ circDist L u + |δ| := by
  have hdef : circDist L u = |u - (round (u / L) : ℝ) * L| := by
    unfold circDist
    rw [mul_comm]
  rw [hdef]
  have h1 := circDist_le_abs_sub_int_mul hL (u + δ) (round (u / L))
  have h2 := abs_add_le (u - (round (u / L) : ℝ) * L) δ
  rw [show u - (round (u / L) : ℝ) * L + δ = u + δ - (round (u / L) : ℝ) * L by ring] at h2
  linarith

/-- The weight `w_2` at a point shifted by `δ`, with `|δ| ≤ 1/(2K)`, is at most `64 · 2^a` times
its value at the unshifted point. -/
lemma gradCell_w2_shift {s a K L u δ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) (hK : 1 ≤ K)
    (hL : 0 < L) (hδ : |δ| ≤ 1 / (2 * K)) :
    gradWeightTwo s a K L (u + δ) ≤ 64 * 2 ^ a * gradWeightTwo s a K L u := by
  have hK0 : 0 < K := by linarith
  have hK1 : K⁻¹ ≤ 1 := (inv_le_one₀ hK0).mpr hK
  have hW := gradCell_w2_nonneg s a K L u
  have h64 : 1 ≤ 64 * (2 : ℝ) ^ a := by
    have : (1 : ℝ) ≤ 2 ^ a := Real.one_le_rpow (by norm_num) ha
    linarith
  have hscale := mul_le_mul_of_nonneg_right h64 hW
  have hd_ge : circDist L u ≤ circDist L (u + δ) + |δ| := by
    have h := gradCell_circDist_add_le hL (u + δ) (-δ)
    rw [show u + δ + -δ = u by ring, abs_neg] at h
    exact h
  rcases le_total (circDist L u) (circDist L (u + δ)) with hle | hle
  · -- The distance grows: the weight decreases.
    have hmono := gradWeightTwo_le_of_circDist_le hs1 ha hK hle
    linarith
  · by_cases hsmall : circDist L u < K⁻¹
    · -- The point lies in the central cell: the weight is the constant `K^{1+a}`.
      have hval : gradWeightTwo s a K L u = K ^ (1 + a) := by
        unfold gradWeightTwo
        rw [ite_eq_left (show circDist L u < 1 by linarith), max_eq_right hsmall.le,
          Real.inv_rpow hK0.le,
          Real.rpow_neg hK0.le, inv_inv]
      have hK' := gradWeightTwo_le_K_pow (L := L) (u := u + δ) hs1 ha hK
      linarith
    · -- The distance is at least `1/K`, so the shifted distance is at least half of it.
      have hd1 : K⁻¹ ≤ circDist L u := not_lt.mp hsmall
      have hdL : circDist L u ≤ L / 2 := circDist_le_half hL u
      have hdnn := gradCell_circDist_nonneg L u
      have hinv : 1 / (2 * K) = K⁻¹ / 2 := by field_simp
      have hdhalf : circDist L u / 2 ≤ circDist L (u + δ) := by
        have h1 : |δ| ≤ circDist L u / 2 := by
          rw [hinv] at hδ
          linarith
        linarith
      have hp : circDist L (circDist L u / 2) = circDist L u / 2 :=
        circDist_of_mem_Icc hL (by linarith) (by linarith)
      have hratio := gradCell_w2_ratio (u := u) (v := circDist L u / 2) (t := circDist L u)
        hs0 hs1 ha hK rfl hp
      have hmono := gradWeightTwo_le_of_circDist_le (u := circDist L u / 2) (v := u + δ) hs1 ha hK
        (by rw [hp]; exact hdhalf)
      linarith

/-! ### The pointwise bound on `R_x` -/

/-- The scaling identity `N^{-s} |v/N|^{-s} = |v|^{-s}`. -/
lemma gradCell_scale_rpow {s N v : ℝ} (hN : 0 < N) :
    N ^ (-s) * |v / N| ^ (-s) = |v| ^ (-s) := by
  rw [abs_div, abs_of_pos hN, Real.div_rpow (abs_nonneg v) hN.le]
  have hA : N ^ (-s) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  field_simp

/-- The cell part of Lemma 5.7, the first bound on `0 < |v| ≤ 3N/4`:
`|R_x(v)| ≤ D D_g C_0 ℓ^{-1} (w_2(x/ℓ) + w_2((x+v/N)/ℓ)) |v|^{-s}`. The hypothesis `hZ` is the
bound on `Z_x`, and `hg2` the bound on `g''`. -/
lemma gradCellR_bound_pointwise {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 ≤ N) (x : ℝ) {v : ℝ} (hv0 : v ≠ 0)
    (hv2 : |v| ≤ 3 * N / 4) {C0 D Dg : ℝ} (hC0 : 0 ≤ C0) (hD : 0 ≤ D)
    (hZ : ∀ y : ℝ, 0 < |y - x| → |gradZx ψ ℓ x y| ≤ D * C0 * ℓ⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) + gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (y / ℓ)))
    (hg2 : ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 → |iteratedDeriv 2 (hurwitzKernel s) r| ≤
      Dg * |r| ^ (-s - 2)) :
    |gradCellR s N ℓ ψ x v| ≤ D * Dg * (C0 * ℓ⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v| ^ (-s) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hr : v / (N : ℝ) ≠ 0 := div_ne_zero hv0 hNpos.ne'
  have hTpos : 0 < |v / (N : ℝ)| := abs_pos.mpr hr
  have hrabs : |v / (N : ℝ)| ≤ 3 / 4 := by
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    linarith
  have hmem : v ∈ gradCellSet N := by
    show ((v / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0
    exact gradSplit_coe_ne_zero hTpos (by linarith)
  have hℓi : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
  have hW0 : 0 ≤ gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
      gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ) :=
    add_nonneg (gradCell_w2_nonneg _ _ _ _ _) (gradCell_w2_nonneg _ _ _ _ _)
  have hE : 0 ≤ D * C0 * ℓ⁻¹ * (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
      gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hD hC0) hℓi) hW0
  have hy : x + v / (N : ℝ) - x = v / (N : ℝ) := by ring
  have hZx : |gradZx ψ ℓ x (x + v / (N : ℝ))| ≤ D * C0 * ℓ⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) :=
    hZ (x + v / N) (by rw [hy]; exact hTpos)
  have hg := hg2 (v / (N : ℝ)) hTpos hrabs
  have hm : 0 ≤ (N : ℝ) ^ (-s) := Real.rpow_nonneg hNpos.le _
  -- The power of `|v/N|` collapses: `|r|^2 |r|^{-s-2} = |r|^{-s}`.
  have hpow : |v / (N : ℝ)| ^ 2 * |v / (N : ℝ)| ^ (-s - 2) = |v / (N : ℝ)| ^ (-s) := by
    rw [show |v / (N : ℝ)| ^ (-s) = |v / (N : ℝ)| ^ ((2 : ℝ) + (-s - 2)) by congr 1; ring,
      Real.rpow_add hTpos, Real.rpow_two]
  have habs : |-(N : ℝ) ^ (-s) * (v / N) ^ 2 * gradZx ψ ℓ x (x + v / N) *
      iteratedDeriv 2 (hurwitzKernel s) (v / N)| =
      (N : ℝ) ^ (-s) * |v / (N : ℝ)| ^ 2 * |gradZx ψ ℓ x (x + v / N)| *
        |iteratedDeriv 2 (hurwitzKernel s) (v / N)| := by
    simp only [abs_mul, abs_neg, abs_pow, abs_of_nonneg hm]
  unfold gradCellR
  rw [habs]
  calc (N : ℝ) ^ (-s) * |v / (N : ℝ)| ^ 2 * |gradZx ψ ℓ x (x + v / N)| *
        |iteratedDeriv 2 (hurwitzKernel s) (v / N)|
      ≤ (N : ℝ) ^ (-s) * |v / (N : ℝ)| ^ 2 *
          (D * C0 * ℓ⁻¹ * (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) *
          (Dg * |v / (N : ℝ)| ^ (-s - 2)) := by
        gcongr
    _ = D * Dg * (C0 * ℓ⁻¹ *
          (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) *
          ((N : ℝ) ^ (-s) * (|v / (N : ℝ)| ^ 2 * |v / (N : ℝ)| ^ (-s - 2))) := by ring
    _ = D * Dg * (C0 * ℓ⁻¹ *
          (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) *
          ((N : ℝ) ^ (-s) * |v / (N : ℝ)| ^ (-s)) := by rw [hpow]
    _ = D * Dg * (C0 * ℓ⁻¹ *
          (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v| ^ (-s) := by
        rw [gradCell_scale_rpow hNpos]

/-! ### Bounds on `0 < |v| ≤ 1/2` and local integrability -/

/-- The first bound of the cell part of Lemma 5.7 on `0 < |v| ≤ 1/2`, in the form where
the weight is comparable to its value at `x/ℓ`: the constant is `D D_g C_0 ℓ^{-1} (1 + 64·2^a)`
times `w_2(x/ℓ)`. -/
lemma gradCellR_bound_small {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) {ψ : ℝ → ℝ}
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 ≤ N) (hK : 1 ≤ (N : ℝ) * ℓ) (x : ℝ) {v : ℝ}
    (hv0 : v ≠ 0) (hv1 : |v| ≤ 1 / 2) {C0 D Dg : ℝ} (hC0 : 0 ≤ C0) (hD : 0 ≤ D)
    (hDg : 0 ≤ Dg)
    (hZ : ∀ y : ℝ, 0 < |y - x| → |gradZx ψ ℓ x y| ≤ D * C0 * ℓ⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) + gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (y / ℓ)))
    (hg2 : ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 → |iteratedDeriv 2 (hurwitzKernel s) r| ≤
      Dg * |r| ^ (-s - 2)) :
    |gradCellR s N ℓ ψ x v| ≤ D * Dg * (C0 * ℓ⁻¹ *
      ((1 + 64 * 2 ^ a) * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ))) * |v| ^ (-s) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNℓ : 0 < (N : ℝ) * ℓ := mul_pos hNpos hℓ
  have hv2 : |v| ≤ 3 * N / 4 := by linarith
  have hpt := gradCellR_bound_pointwise hs0 hs1 hℓ N hN x hv0 hv2 hC0 hD hZ hg2
  -- The shift `(x + v/N)/ℓ = x/ℓ + v/(Nℓ)` has size at most `1/(2K)`.
  have hsh : (x + v / (N : ℝ)) / ℓ = x / ℓ + v / ((N : ℝ) * ℓ) := by
    rw [add_div, div_div]
  have hδ : |v / ((N : ℝ) * ℓ)| ≤ 1 / (2 * ((N : ℝ) * ℓ)) := by
    rw [abs_div, abs_of_pos hNℓ]
    calc |v| / ((N : ℝ) * ℓ) ≤ (1 / 2) / ((N : ℝ) * ℓ) :=
          div_le_div_of_nonneg_right hv1 hNℓ.le
      _ = 1 / (2 * ((N : ℝ) * ℓ)) := by rw [div_div]
  have hw := gradCell_w2_shift (u := x / ℓ) (δ := v / ((N : ℝ) * ℓ)) hs0 hs1 ha hK
    (inv_pos.mpr hℓ) hδ
  rw [← hsh] at hw
  have hsum : gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
      gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ) ≤
      (1 + 64 * 2 ^ a) * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) := by
    have h' : (1 + 64 * (2 : ℝ) ^ a) * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) =
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
          64 * 2 ^ a * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) := by ring
    rw [h']
    linarith
  have hrp : 0 ≤ |v| ^ (-s) := Real.rpow_nonneg (abs_nonneg v) _
  have hC0ℓ : 0 ≤ C0 * ℓ⁻¹ := mul_nonneg hC0 (inv_nonneg.mpr hℓ.le)
  have hDDg : 0 ≤ D * Dg := mul_nonneg hD hDg
  calc |gradCellR s N ℓ ψ x v|
      ≤ D * Dg * (C0 * ℓ⁻¹ *
          (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v| ^ (-s) := hpt
    _ ≤ D * Dg * (C0 * ℓ⁻¹ * ((1 + 64 * 2 ^ a) *
          gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ))) * |v| ^ (-s) := by
        apply mul_le_mul_of_nonneg_right _ hrp
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hC0ℓ) hDDg

/-! ### Integrability on `[-1/2, 1/2]` and the integral bound -/

/-- The power `|v|^{-s}` is interval integrable on `[0, b]`, for `s < 1` and `0 ≤ b`. -/
lemma intervalIntegrable_abs_rpow_right {s b : ℝ} (hs1 : s < 1) (hb : 0 ≤ b) :
    IntervalIntegrable (fun v : ℝ => |v| ^ (-s)) volume 0 b := by
  have hpos : IntervalIntegrable (fun x : ℝ => x ^ (-s)) volume 0 b :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine IntervalIntegrable.congr_uIoo hpos ?_
  intro t ht
  rw [uIoo, min_eq_left hb, max_eq_right hb] at ht
  simp only
  rw [abs_of_pos ht.1]

/-- Reflection: `|v|^{-s}` is interval integrable on `[-b, 0]` once it is on `[0, b]`. -/
lemma intervalIntegrable_abs_rpow_left {s b : ℝ}
    (h1 : IntervalIntegrable (fun v : ℝ => |v| ^ (-s)) volume 0 b) :
    IntervalIntegrable (fun v : ℝ => |v| ^ (-s)) volume (-b) 0 := by
  rw [IntervalIntegrable.iff_comp_neg, neg_neg, neg_zero]
  refine IntervalIntegrable.congr_uIoo h1.symm ?_
  intro t _
  simp only
  rw [abs_neg]

/-- The power `|v|^{-s}` is interval integrable on the symmetric interval `[-b, b]`. -/
lemma intervalIntegrable_abs_rpow_symm {s b : ℝ} (hs1 : s < 1) (hb : 0 ≤ b) :
    IntervalIntegrable (fun v : ℝ => |v| ^ (-s)) volume (-b) b :=
  (intervalIntegrable_abs_rpow_left (intervalIntegrable_abs_rpow_right hs1 hb)).trans
    (intervalIntegrable_abs_rpow_right hs1 hb)

/-- The integral `∫_{-b}^{b} |v|^{-s} dv = 2 b^{1-s}/(1-s)`. -/
lemma intervalIntegral_abs_rpow_symm {s b : ℝ} (hs1 : s < 1) (hb : 0 ≤ b) :
    ∫ v in (-b)..b, |v| ^ (-s) = 2 * b ^ (1 - s) / (1 - s) := by
  have hi1 : IntervalIntegrable (fun v : ℝ => |v| ^ (-s)) volume 0 b :=
    intervalIntegrable_abs_rpow_right hs1 hb
  have hi0 : IntervalIntegrable (fun v : ℝ => |v| ^ (-s)) volume (-b) 0 :=
    intervalIntegrable_abs_rpow_left hi1
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1]
  have hneg : ∫ v in (-b)..0, |v| ^ (-s) = ∫ v in (0 : ℝ)..b, |v| ^ (-s) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := b) (fun v : ℝ => |v| ^ (-s))
    simp only [neg_zero, abs_neg] at h
    exact h.symm
  rw [hneg]
  have hpos : ∫ v in (0 : ℝ)..b, |v| ^ (-s) = ∫ v in (0 : ℝ)..b, v ^ (-s) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hb] at ht
    simp only
    rw [abs_of_nonneg ht.1]
  rw [hpos, integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]
  rw [show -s + 1 = 1 - s by ring]
  ring

/-- A continuous function on an open interval, dominated by an integrable function, is integrable
on that interval. -/
lemma integrableOn_Ioo_of_bound {f g : ℝ → ℝ} {p q : ℝ} (hcont : ContinuousOn f (Ioo p q))
    (hg : IntegrableOn g (Ioo p q)) (hbd : ∀ v ∈ Ioo p q, |f v| ≤ g v) :
    IntegrableOn f (Ioo p q) := by
  refine Integrable.mono' hg (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact ae_of_all _ fun v hv => by rw [Real.norm_eq_abs]; exact hbd v hv

/-- A nonzero point of modulus at most `1/2` lies in `gradCellSet N` for `N ≥ 2`. -/
lemma mem_gradCellSet_of_small {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv0 : v ≠ 0) (hv : |v| ≤ 1 / 2) :
    v ∈ gradCellSet N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hr : v / (N : ℝ) ≠ 0 := div_ne_zero hv0 hNpos.ne'
  have h1 : |v / (N : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos hNpos, div_lt_one hNpos]
    linarith
  show ((v / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0
  exact gradSplit_coe_ne_zero (abs_pos.mpr hr) h1

/-- Local integrability of `R_x` at zero: `R_x` is interval integrable on `[-1/2, 1/2]`. -/
lemma gradCellR_intervalIntegrable {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 ≤ N)
    (hK : 1 ≤ (N : ℝ) * ℓ) (x : ℝ) {C0 D Dg : ℝ} (hC0 : 0 ≤ C0) (hD : 0 ≤ D) (hDg : 0 ≤ Dg)
    (hZ : ∀ y : ℝ, 0 < |y - x| → |gradZx ψ ℓ x y| ≤ D * C0 * ℓ⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) + gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (y / ℓ)))
    (hg2 : ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 → |iteratedDeriv 2 (hurwitzKernel s) r| ≤
      Dg * |r| ^ (-s - 2)) :
    IntervalIntegrable (gradCellR s N ℓ ψ x) volume (-(1 / 2)) (1 / 2) := by
  have hcont : ContinuousOn (gradCellR s N ℓ ψ x) (gradCellSet N) :=
    (contDiffOn_gradCellR hs0 hs1 hψ hℓ N x).continuousOn
  have hgI : IntegrableOn (fun v : ℝ => D * Dg * (C0 * ℓ⁻¹ *
      ((1 + 64 * 2 ^ a) * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ))) * |v| ^ (-s))
      (Ioo (-(1 / 2)) (1 / 2)) volume := by
    have h := (intervalIntegrable_abs_rpow_symm hs1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).const_mul
      (D * Dg * (C0 * ℓ⁻¹ * ((1 + 64 * 2 ^ a) * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ))))
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp h
  have hL : IntegrableOn (gradCellR s N ℓ ψ x) (Ioo (-(1 / 2)) 0) volume := by
    refine integrableOn_Ioo_of_bound (hcont.mono ?_)
      (hgI.mono_set (Ioo_subset_Ioo le_rfl (by norm_num))) ?_
    · intro v hv
      exact mem_gradCellSet_of_small hN hv.2.ne (abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩)
    · intro v hv
      exact gradCellR_bound_small hs0 hs1 ha hℓ N hN hK x hv.2.ne
        (abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩) hC0 hD hDg hZ hg2
  have hR : IntegrableOn (gradCellR s N ℓ ψ x) (Ioo 0 (1 / 2)) volume := by
    refine integrableOn_Ioo_of_bound (hcont.mono ?_)
      (hgI.mono_set (Ioo_subset_Ioo (by norm_num) le_rfl)) ?_
    · intro v hv
      exact mem_gradCellSet_of_small hN hv.1.ne' (abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩)
    · intro v hv
      exact gradCellR_bound_small hs0 hs1 ha hℓ N hN hK x hv.1.ne'
        (abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩) hC0 hD hDg hZ hg2
  have hIoo : IntegrableOn (gradCellR s N ℓ ψ x) (Ioo (-(1 / 2)) (1 / 2)) volume := by
    rw [← Set.Ioo_union_Ico_eq_Ioo (by norm_num : (-(1 / 2) : ℝ) < 0) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact hL.union ((integrableOn_Ico_iff_integrableOn_Ioo).mpr hR)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr hIoo

/-- The integral bound of the cell part of Lemma 5.7:
`∫_{-1/2}^{1/2} |R_x| ≤ D D_g C_0 ℓ^{-1} (1 + 64·2^a) w_2(x/ℓ) · 2 (1/2)^{1-s}/(1-s)`. -/
lemma gradCellR_integral_le {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 ≤ N)
    (hK : 1 ≤ (N : ℝ) * ℓ) (x : ℝ) {C0 D Dg : ℝ} (hC0 : 0 ≤ C0) (hD : 0 ≤ D) (hDg : 0 ≤ Dg)
    (hZ : ∀ y : ℝ, 0 < |y - x| → |gradZx ψ ℓ x y| ≤ D * C0 * ℓ⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) + gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (y / ℓ)))
    (hg2 : ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 → |iteratedDeriv 2 (hurwitzKernel s) r| ≤
      Dg * |r| ^ (-s - 2)) :
    ∫ v in (-(1 / 2))..(1 / 2), |gradCellR s N ℓ ψ x v| ≤
      D * Dg * (C0 * ℓ⁻¹ * ((1 + 64 * 2 ^ a) * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ))) *
        (2 * (1 / 2) ^ (1 - s) / (1 - s)) := by
  have hI := gradCellR_intervalIntegrable hs0 hs1 ha hψ hℓ N hN hK x hC0 hD hDg hZ hg2
  have hIabs : IntervalIntegrable (fun v => |gradCellR s N ℓ ψ x v|) volume (-(1 / 2)) (1 / 2) :=
    hI.abs
  have hg : IntervalIntegrable (fun v : ℝ => D * Dg * (C0 * ℓ⁻¹ *
      ((1 + 64 * 2 ^ a) * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ))) * |v| ^ (-s))
      volume (-(1 / 2)) (1 / 2) :=
    (intervalIntegrable_abs_rpow_symm hs1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).const_mul _
  have hae : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 0 := by
    rw [ae_iff]
    simp
  have hle : (fun v => |gradCellR s N ℓ ψ x v|) ≤ᵐ[volume.restrict (Icc (-(1 / 2)) (1 / 2))]
      (fun v : ℝ => D * Dg * (C0 * ℓ⁻¹ *
        ((1 + 64 * 2 ^ a) * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ))) * |v| ^ (-s)) := by
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hae] with v hv0 hvI
    exact gradCellR_bound_small hs0 hs1 ha hℓ N hN hK x hv0
      (abs_le.mpr ⟨hvI.1, hvI.2⟩) hC0 hD hDg hZ hg2
  have hmono := intervalIntegral.integral_mono_ae_restrict (by norm_num) hIabs hg hle
  rw [intervalIntegral.integral_const_mul, intervalIntegral_abs_rpow_symm hs1 (by norm_num)] at hmono
  exact hmono

end Riesz1

end
