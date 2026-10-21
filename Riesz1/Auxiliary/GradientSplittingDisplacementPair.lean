/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingDisplacementEvent
public import Riesz1.Auxiliary.GradientSplittingDisplacementKernel
public import Riesz1.Auxiliary.GradientSplittingDifferencesFull

/-!
# The displacement pair bound: kernel increments and the three product estimates

The displacement part of Lemma 5.7. The kernel increments
`h(r) - h(k/N)` (mean value and direct cases split at `N = 4^{2/(1-s/2)}`), the lattice values of
`h` and `h'`, and the bound on one pair of the displacement sum `V^{(1)}`.
-/

@[expose] public section

open scoped ContDiff

namespace Riesz1

noncomputable section

/-- A power identity for the spacing `K^{-ε}|k|/N`: `(lam⁻¹ (A/N))^e = lam^{-e} N^{-e} A^e`. -/
lemma rpow_inv_lam_div {lam A N e : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hN : 0 < N) :
    (lam⁻¹ * (A / N)) ^ e = lam ^ (-e) * N ^ (-e) * A ^ e := by
  rw [Real.mul_rpow (inv_nonneg.mpr hlam.le) (div_nonneg hA.le hN.le)]
  rw [Real.inv_rpow hlam.le, Real.div_rpow hA.le hN.le]
  rw [Real.rpow_neg hlam.le, Real.rpow_neg hN.le]
  ring

/-- The threshold `N₀ = 4^{2/(1-s/2)}`: above it, `N^{1-ε-s/2} ≥ 4`. -/
lemma four_le_rpow_of_threshold {s ε N : ℝ} (_hs1 : s < 1) (hε : 0 < ε)
    (hεs : ε < (1 - s / 2) / 8) (hN : (4 : ℝ) ^ (2 / (1 - s / 2)) ≤ N) :
    4 ≤ N ^ (1 - ε - s / 2) := by
  have hpos : (0 : ℝ) < 1 - s / 2 := by linarith
  have hN1 : (1 : ℝ) ≤ (4 : ℝ) ^ (2 / (1 - s / 2)) :=
    Real.one_le_rpow (by norm_num) (div_nonneg (by norm_num) hpos.le)
  have hexp : (1 - s / 2) / 2 ≤ 1 - ε - s / 2 := by linarith
  have h2s : (2 : ℝ) - s ≠ 0 := by
    intro h
    linarith
  have hexp1 : 2 / (1 - s / 2) * ((1 - s / 2) / 2) = 1 := by
    have h' : (1 : ℝ) - s / 2 = (2 - s) / 2 := by ring
    rw [h']
    field_simp
  have h1 : ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ ((1 - s / 2) / 2) = 4 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4), hexp1, Real.rpow_one]
  calc (4 : ℝ) = ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ ((1 - s / 2) / 2) := h1.symm
    _ ≤ N ^ ((1 - s / 2) / 2) := Real.rpow_le_rpow (by positivity) hN (by linarith)
    _ ≤ N ^ (1 - ε - s / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp

/-- Large windows: the mean value bound for `h` between `t = k/N` and `D = r` gives
`N^{-s} |h(D) - h(t)| ≤ C lam^{s+2} |k|^{-1-s/2}` with `lam = K^ε`. -/
lemma pair_kernel_caseA {s C₁ lam N κ D : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC₀ : 0 ≤ C₁)
    (hC₁ : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 → |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * u ^ (-s - 1))
    (hN : 0 < N) (hlam1 : 1 ≤ lam) (hκ0 : κ ≠ 0) (hκN : 2 * |κ| ≤ N) (hDκ : 0 < D * κ)
    (hF2a : lam⁻¹ * |κ| ≤ N * |D|) (hF1 : |N * D - κ| ≤ lam * |κ| ^ (s / 2))
    (hN34 : lam * |κ| ^ (s / 2) ≤ N / 4) :
    N ^ (-s) * |gradKernelH s D - gradKernelH s (κ / N)| ≤ C₁ * lam ^ (s + 2) * |κ| ^ (-1 - s / 2) := by
  have hκa : 0 < |κ| := abs_pos.mpr hκ0
  have hlam : 0 < lam := by linarith
  have hNs : 0 ≤ N ^ (-s) := Real.rpow_nonneg hN.le _
  set t := κ / N with ht
  have hta : |t| = |κ| / N := by rw [ht, abs_div, abs_of_pos hN]
  have hDt' : |D - t| ≤ lam * |κ| ^ (s / 2) / N := by
    have e : D - t = (N * D - κ) / N := by
      rw [ht]
      field_simp
    rw [e, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right hF1 hN.le
  have hDt4 : |D - t| ≤ 1 / 4 := by
    calc |D - t| ≤ lam * |κ| ^ (s / 2) / N := hDt'
      _ ≤ (N / 4) / N := div_le_div_of_nonneg_right hN34 hN.le
      _ = 1 / 4 := by field_simp
  have ht34 : |t| ≤ 1 / 2 := by
    rw [hta, div_le_iff₀ hN]
    linarith
  have hD34 : |D| ≤ 3 / 4 := by
    have h := abs_add_le t (D - t)
    rw [show t + (D - t) = D by ring] at h
    linarith
  have hDt_sign : 0 < D * t := by
    have e : D * t = D * κ / N := by
      rw [ht]
      ring
    rw [e]
    exact div_pos hDκ hN
  have hμr : lam⁻¹ * |t| ≤ |D| := by
    rw [hta, show lam⁻¹ * (|κ| / N) = (lam⁻¹ * |κ|) / N by ring, div_le_iff₀ hN]
    linarith [hF2a, mul_comm N |D|]
  have hμ : 0 < lam⁻¹ := inv_pos.mpr hlam
  have hμ1 : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam1
  have hmvt := gradKernel_sub_le_sign hs0 hs1 hC₀ hC₁ hμ hμ1 hDt_sign hμr
    (by linarith) hD34
  rw [hta] at hmvt
  rw [rpow_inv_lam_div hlam hκa hN, show -(-s - 1) = s + 1 by ring] at hmvt
  have hκpow : |κ| ^ (-s - 1) * |κ| ^ (s / 2) = |κ| ^ (-1 - s / 2) := by
    rw [← Real.rpow_add hκa]
    congr 1
    ring
  have hNpow : N ^ (-s) * N ^ (s + 1) = N := by
    rw [← Real.rpow_add hN, show -s + (s + 1) = (1 : ℝ) by ring, Real.rpow_one]
  have hlampow : lam ^ (s + 2) = lam ^ (s + 1) * lam := by
    rw [show s + 2 = (s + 1) + 1 by ring, Real.rpow_add hlam, Real.rpow_one]
  calc N ^ (-s) * |gradKernelH s D - gradKernelH s t|
      ≤ N ^ (-s) * (C₁ * (lam ^ (s + 1) * N ^ (s + 1) * |κ| ^ (-s - 1)) * |D - t|) :=
        mul_le_mul_of_nonneg_left hmvt hNs
    _ ≤ N ^ (-s) * (C₁ * (lam ^ (s + 1) * N ^ (s + 1) * |κ| ^ (-s - 1)) * (lam * |κ| ^ (s / 2) / N)) := by
        apply mul_le_mul_of_nonneg_left _ hNs
        apply mul_le_mul_of_nonneg_left hDt' 
        exact mul_nonneg hC₀ (by positivity)
    _ = C₁ * lam ^ (s + 2) * |κ| ^ (-1 - s / 2) := by
        rw [hlampow]
        have e : N ^ (-s) * (C₁ * (lam ^ (s + 1) * N ^ (s + 1) * |κ| ^ (-s - 1)) * (lam * |κ| ^ (s / 2) / N))
            = C₁ * (lam ^ (s + 1) * lam) * (N ^ (-s) * N ^ (s + 1)) * (|κ| ^ (-s - 1) * |κ| ^ (s / 2)) / N := by
          ring
        rw [e, hNpow, hκpow]
        field_simp

/-- Small windows: the individual kernel bounds at `D` and `t` give
`N^{-s} |h(D) - h(t)| ≤ C (2^s + 1) N₀^{1-s/2} lam^{s+2} |k|^{-1-s/2}`, when `1 ≤ lam ≤ 2`,
`|D| ≤ 3/4` and `|k| ≤ N₀`. -/
lemma pair_kernel_caseB {s C₁ lam N κ D N₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC₀ : 0 ≤ C₁)
    (hC₁ : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 → |gradKernelH s u| ≤ C₁ * |u| ^ (-s))
    (hN : 0 < N) (hlam1 : 1 ≤ lam) (hlam2 : lam ≤ 2) (hκ0 : κ ≠ 0) (hκN : 2 * |κ| ≤ N)
    (hDκ : 0 < D * κ) (hF2a : lam⁻¹ * |κ| ≤ N * |D|) (hD34 : |D| ≤ 3 / 4)
    (hN₀ : 0 < N₀) (hκN₀ : |κ| ≤ N₀) :
    N ^ (-s) * |gradKernelH s D - gradKernelH s (κ / N)|
      ≤ C₁ * (2 ^ s + 1) * N₀ ^ (1 - s / 2) * lam ^ (s + 2) * |κ| ^ (-1 - s / 2) := by
  have hκa : 0 < |κ| := abs_pos.mpr hκ0
  have hlam : 0 < lam := by linarith
  have hNs : 0 ≤ N ^ (-s) := Real.rpow_nonneg hN.le _
  set t := κ / N with ht
  have hta : |t| = |κ| / N := by rw [ht, abs_div, abs_of_pos hN]
  have ht34 : |t| ≤ 3 / 4 := by
    rw [hta, div_le_iff₀ hN]
    linarith
  have ht0 : 0 < |t| := by
    rw [hta]
    exact div_pos hκa hN
  have hD0 : D ≠ 0 := by
    rintro rfl
    simp at hDκ
  have hDa : 0 < |D| := abs_pos.mpr hD0
  have hDlow : lam⁻¹ * |κ| / N ≤ |D| := by
    rw [div_le_iff₀ hN]
    linarith [hF2a, mul_comm N |D|]
  have hDpos : 0 < lam⁻¹ * |κ| / N := by
    have : 0 < lam⁻¹ := inv_pos.mpr hlam
    positivity
  have hDh : |gradKernelH s D| ≤ C₁ * |D| ^ (-s) := hC₁ D hDa hD34
  have hDpow : |D| ^ (-s) ≤ (lam⁻¹ * |κ| / N) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hDpos hDlow (by linarith)
  have hDpow2 : (lam⁻¹ * |κ| / N) ^ (-s) = lam ^ s * N ^ s * |κ| ^ (-s) := by
    rw [show lam⁻¹ * |κ| / N = lam⁻¹ * (|κ| / N) by ring, rpow_inv_lam_div hlam hκa hN,
      neg_neg]
  have htpow : |gradKernelH s t| ≤ C₁ * |t| ^ (-s) := hC₁ t ht0 ht34
  have htpow2 : |t| ^ (-s) = |κ| ^ (-s) * N ^ s := by
    rw [hta, Real.div_rpow hκa.le hN.le, Real.rpow_neg hN.le, div_inv_eq_mul]
  have hNN : N ^ (-s) * N ^ s = 1 := by
    rw [Real.rpow_neg hN.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hN _).ne']
  have hmain : N ^ (-s) * |gradKernelH s D - gradKernelH s t|
      ≤ C₁ * (lam ^ s + 1) * |κ| ^ (-s) := by
    have h1 := abs_sub (gradKernelH s D) (gradKernelH s t)
    have hDb : |gradKernelH s D| ≤ C₁ * (lam ^ s * N ^ s * |κ| ^ (-s)) := by
      calc |gradKernelH s D| ≤ C₁ * |D| ^ (-s) := hDh
        _ ≤ C₁ * (lam⁻¹ * |κ| / N) ^ (-s) := mul_le_mul_of_nonneg_left hDpow hC₀
        _ = C₁ * (lam ^ s * N ^ s * |κ| ^ (-s)) := by rw [hDpow2]
    have htb : |gradKernelH s t| ≤ C₁ * (|κ| ^ (-s) * N ^ s) := by
      rw [← htpow2]
      exact htpow
    calc N ^ (-s) * |gradKernelH s D - gradKernelH s t|
        ≤ N ^ (-s) * (|gradKernelH s D| + |gradKernelH s t|) := mul_le_mul_of_nonneg_left h1 hNs
      _ ≤ N ^ (-s) * (C₁ * (lam ^ s * N ^ s * |κ| ^ (-s)) + C₁ * (|κ| ^ (-s) * N ^ s)) :=
          mul_le_mul_of_nonneg_left (add_le_add hDb htb) hNs
      _ = C₁ * (lam ^ s + 1) * |κ| ^ (-s) * (N ^ (-s) * N ^ s) := by ring
      _ = C₁ * (lam ^ s + 1) * |κ| ^ (-s) := by rw [hNN, mul_one]
  have hW : |κ| ^ (-s) ≤ N₀ ^ (1 - s / 2) * |κ| ^ (-1 - s / 2) := by
    have e : |κ| ^ (-s) = |κ| ^ (-1 - s / 2) * |κ| ^ (1 - s / 2) := by
      rw [← Real.rpow_add hκa]
      congr 1
      ring
    rw [e]
    have hle : |κ| ^ (1 - s / 2) ≤ N₀ ^ (1 - s / 2) :=
      Real.rpow_le_rpow hκa.le hκN₀ (by linarith)
    have hpos : 0 ≤ |κ| ^ (-1 - s / 2) := Real.rpow_nonneg hκa.le _
    calc |κ| ^ (-1 - s / 2) * |κ| ^ (1 - s / 2) ≤ |κ| ^ (-1 - s / 2) * N₀ ^ (1 - s / 2) :=
          mul_le_mul_of_nonneg_left hle hpos
      _ = N₀ ^ (1 - s / 2) * |κ| ^ (-1 - s / 2) := mul_comm _ _
  have hlams : lam ^ s ≤ 2 ^ s := Real.rpow_le_rpow hlam.le hlam2 hs0.le
  have hl2 : 1 ≤ lam ^ (s + 2) := Real.one_le_rpow hlam1 (by linarith)
  have hQ : 0 ≤ C₁ * (2 ^ s + 1) * N₀ ^ (1 - s / 2) * |κ| ^ (-1 - s / 2) := by
    have : 0 ≤ N₀ ^ (1 - s / 2) := Real.rpow_nonneg hN₀.le _
    have : 0 ≤ |κ| ^ (-1 - s / 2) := Real.rpow_nonneg hκa.le _
    positivity
  calc N ^ (-s) * |gradKernelH s D - gradKernelH s t|
      ≤ C₁ * (lam ^ s + 1) * |κ| ^ (-s) := hmain
    _ ≤ C₁ * (2 ^ s + 1) * (N₀ ^ (1 - s / 2) * |κ| ^ (-1 - s / 2)) := by
        apply mul_le_mul _ hW (Real.rpow_nonneg hκa.le _)
        · exact mul_nonneg hC₀ (by positivity)
        · exact mul_le_mul_of_nonneg_left (by linarith) hC₀
    _ = C₁ * (2 ^ s + 1) * N₀ ^ (1 - s / 2) * |κ| ^ (-1 - s / 2) := by ring
    _ ≤ C₁ * (2 ^ s + 1) * N₀ ^ (1 - s / 2) * |κ| ^ (-1 - s / 2) * lam ^ (s + 2) :=
        le_mul_of_one_le_right hQ hl2
    _ = C₁ * (2 ^ s + 1) * N₀ ^ (1 - s / 2) * lam ^ (s + 2) * |κ| ^ (-1 - s / 2) := by ring

/-- The kernel bound on one pair: for every admissible pair `(i,j)`, with `K = Nℓ` and
`lam = K^ε`, `N^{-s} |h(r) - h(k/N)| ≤ C lam^{s+2} |k|^{-1-s/2}`. The threshold
`N₀ = 4^{2/(1-s/2)}` separates the mean value case from the direct case. -/
lemma gradKernel_pair_bound {s C₁ K N κ D ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hC₀ : 0 ≤ C₁)
    (hC_der : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 → |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * u ^ (-s - 1))
    (hC_val : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 → |gradKernelH s u| ≤ C₁ * |u| ^ (-s))
    (hK1 : 1 ≤ K) (hKN : K ≤ N) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8) (hN : 0 < N)
    (hκ0 : κ ≠ 0) (hκN : 2 * |κ| ≤ N) (hDκ : 0 < D * κ) (hF2a : K ^ (-ε) * |κ| ≤ N * |D|)
    (hF1 : |N * D - κ| ≤ K ^ ε * |κ| ^ (s / 2))
    (hD34 : (4 : ℝ) ^ (2 / (1 - s / 2)) > N → |D| ≤ 3 / 4) :
    N ^ (-s) * |gradKernelH s D - gradKernelH s (κ / N)|
      ≤ C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) * (K ^ ε) ^ (s + 2)
        * |κ| ^ (-1 - s / 2) := by
  have hK0 : 0 < K := by linarith
  have hlam1 : 1 ≤ K ^ ε := Real.one_le_rpow hK1 hε.le
  have hF2a' : (K ^ ε)⁻¹ * |κ| ≤ N * |D| := by
    rw [← Real.rpow_neg hK0.le]
    exact hF2a
  have hpos : (0 : ℝ) < 1 - s / 2 := by linarith
  have hN₀pos : (0 : ℝ) < (4 : ℝ) ^ (2 / (1 - s / 2)) := by positivity
  have hN₀one : (1 : ℝ) ≤ (4 : ℝ) ^ (2 / (1 - s / 2)) :=
    Real.one_le_rpow (by norm_num) (div_nonneg (by norm_num) hpos.le)
  have hconst : 1 ≤ (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) := by
    have h1 : (1 : ℝ) ≤ ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) :=
      Real.one_le_rpow hN₀one (by linarith)
    have h2 : (1 : ℝ) ≤ 2 ^ s + 1 := by
      have : (0 : ℝ) ≤ 2 ^ s := Real.rpow_nonneg (by norm_num) _
      linarith
    nlinarith
  by_cases hNN : (4 : ℝ) ^ (2 / (1 - s / 2)) ≤ N
  · -- large windows: the mean value argument
    have hKε : K ^ ε ≤ N ^ ε := Real.rpow_le_rpow hK0.le hKN hε.le
    have hκs : |κ| ^ (s / 2) ≤ N ^ (s / 2) :=
      Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg κ]) (by linarith)
    have hprod : K ^ ε * |κ| ^ (s / 2) ≤ N ^ (ε + s / 2) := by
      rw [Real.rpow_add hN]
      exact mul_le_mul hKε hκs (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hN.le _)
    have hx4 : N ^ (ε + s / 2) * 4 ≤ N := by
      have h4 := four_le_rpow_of_threshold hs1 hε hεs hNN
      have hxx : N ^ (ε + s / 2) * N ^ (1 - ε - s / 2) = N := by
        rw [← Real.rpow_add hN, show ε + s / 2 + (1 - ε - s / 2) = 1 by ring, Real.rpow_one]
      calc N ^ (ε + s / 2) * 4 ≤ N ^ (ε + s / 2) * N ^ (1 - ε - s / 2) :=
            mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hN.le _)
        _ = N := hxx
    have hN34 : K ^ ε * |κ| ^ (s / 2) ≤ N / 4 := by linarith
    have hcase := pair_kernel_caseA hs0 hs1 hC₀ hC_der hN hlam1 hκ0 hκN hDκ hF2a' hF1 hN34
    have hC1le : C₁ ≤ C₁ * ((2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2)) :=
      le_mul_of_one_le_right hC₀ hconst
    have hpow : 0 ≤ (K ^ ε) ^ (s + 2) := Real.rpow_nonneg (by positivity) _
    have hκp : 0 ≤ |κ| ^ (-1 - s / 2) := Real.rpow_nonneg (abs_nonneg _) _
    calc N ^ (-s) * |gradKernelH s D - gradKernelH s (κ / N)|
        ≤ C₁ * (K ^ ε) ^ (s + 2) * |κ| ^ (-1 - s / 2) := by
          exact hcase
      _ ≤ C₁ * ((2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2)) * (K ^ ε) ^ (s + 2)
            * |κ| ^ (-1 - s / 2) := by
          apply mul_le_mul_of_nonneg_right _ hκp
          exact mul_le_mul_of_nonneg_right hC1le hpow
      _ = C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) * (K ^ ε) ^ (s + 2)
            * |κ| ^ (-1 - s / 2) := by ring
  · -- small windows: the direct argument, with `K^ε ≤ 2`
    have hNN' : N < (4 : ℝ) ^ (2 / (1 - s / 2)) := not_le.mp hNN
    have hKN0 : K ≤ (4 : ℝ) ^ (2 / (1 - s / 2)) := by linarith
    have hlam2 : K ^ ε ≤ 2 := by
      have h1 : K ^ ε ≤ ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ ε := Real.rpow_le_rpow hK0.le hKN0 hε.le
      have h2 : ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ ε = (4 : ℝ) ^ (2 / (1 - s / 2) * ε) := by
        rw [← Real.rpow_mul (by norm_num)]
      have h3 : 2 / (1 - s / 2) * ε ≤ 1 / 4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        linarith
      have h4 : (4 : ℝ) ^ (2 / (1 - s / 2) * ε) ≤ (4 : ℝ) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
      have h5 : (4 : ℝ) ^ ((1 : ℝ) / 4) ≤ (4 : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h6 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
        rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    have hκN₀ : |κ| ≤ (4 : ℝ) ^ (2 / (1 - s / 2)) := by
      linarith [abs_nonneg κ]
    have hcase := pair_kernel_caseB hs0 hs1 hC₀ hC_val hN hlam1 hlam2 hκ0 hκN hDκ hF2a'
      (hD34 hNN') hN₀pos hκN₀
    exact hcase

/-- Below the threshold `N < 4^{2/(1-s/2)}`, `K^ε ≤ 2` for `K ≤ N`. -/
lemma rpow_le_two_of_lt_threshold {s ε K N : ℝ} (_hs1 : s < 1) (hε : 0 < ε)
    (hεs : ε < (1 - s / 2) / 8) (hK0 : 0 < K) (hKN : K ≤ N)
    (hNN : N < (4 : ℝ) ^ (2 / (1 - s / 2))) : K ^ ε ≤ 2 := by
  have hpos : (0 : ℝ) < 1 - s / 2 := by linarith
  have hKN0 : K ≤ (4 : ℝ) ^ (2 / (1 - s / 2)) := by linarith
  have h1 : K ^ ε ≤ ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ ε := Real.rpow_le_rpow hK0.le hKN0 hε.le
  have h2 : ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ ε = (4 : ℝ) ^ (2 / (1 - s / 2) * ε) := by
    rw [← Real.rpow_mul (by norm_num)]
  have h3 : 2 / (1 - s / 2) * ε ≤ 1 / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith
  have h4 : (4 : ℝ) ^ (2 / (1 - s / 2) * ε) ≤ (4 : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
  have h5 : (4 : ℝ) ^ ((1 : ℝ) / 4) ≤ (4 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h6 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith

/-- Splitting one pair of the displacement sum: with `u, v` the values of `Z_x` at the two
endpoints, `p, q` the values of `Z`, and `H₁, H₀, Hp` the values of `h` and `h'`, the difference
`2n (u H₁ - v H₀) - 2n (p - q) Hp` with `n ≥ 0` is bounded by the three product estimates. -/
lemma V1_pair_split {n u v p q H1 H0 Hp : ℝ} (hn : 0 ≤ n) :
    |2 * n * (u * H1 - v * H0) - 2 * n * (p - q) * Hp|
      ≤ 2 * (|u| * (n * |H1 - H0|)) + 2 * (|u - v| * (n * |H0|))
        + 2 * (|p - q| * (n * |Hp|)) := by
  have e : 2 * n * (u * H1 - v * H0) - 2 * n * (p - q) * Hp
      = 2 * (u * (n * (H1 - H0))) + 2 * ((u - v) * (n * H0)) - 2 * ((p - q) * (n * Hp)) := by
    ring
  rw [e]
  have h1 : |2 * (u * (n * (H1 - H0))) + 2 * ((u - v) * (n * H0)) - 2 * ((p - q) * (n * Hp))|
      ≤ |2 * (u * (n * (H1 - H0)))| + |2 * ((u - v) * (n * H0))| + |2 * ((p - q) * (n * Hp))| := by
    refine le_trans (abs_sub _ _) ?_
    have := abs_add_le (2 * (u * (n * (H1 - H0)))) (2 * ((u - v) * (n * H0)))
    have h2 := abs_mul (2:ℝ) (u * (n * (H1 - H0)))
    linarith
  have hA : |2 * (u * (n * (H1 - H0)))| = 2 * (|u| * (n * |H1 - H0|)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hn, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hB : |2 * ((u - v) * (n * H0))| = 2 * (|u - v| * (n * |H0|)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hn, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hC : |2 * ((p - q) * (n * Hp))| = 2 * (|p - q| * (n * |Hp|)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hn, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The kernel values at the lattice point `t = k/N`, with `n = N^{-s}`: `n |h(t)| ≤ C |k|^{-s}`
and `n |h'(t)| ≤ C N |k|^{-s-1}`, from the kernel bounds at `|t| ≤ 3/4`. -/
lemma kernel_lattice_bounds {s C₁ N κ : ℝ} (_hs0 : 0 < s) (_hC₁0 : 0 ≤ C₁) (hN : 0 < N)
    (hκa : 0 < |κ|) (ht34 : |κ / N| ≤ 3 / 4)
    (hC_val : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 → |gradKernelH s u| ≤ C₁ * |u| ^ (-s))
    (hC_der : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 →
      |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * |u| ^ (-s - 1)) :
    N ^ (-s) * |gradKernelH s (κ / N)| ≤ C₁ * |κ| ^ (-s)
      ∧ N ^ (-s) * |iteratedDeriv 1 (gradKernelH s) (κ / N)| ≤ C₁ * N * |κ| ^ (-s - 1) := by
  have hta : |κ / N| = |κ| / N := by rw [abs_div, abs_of_pos hN]
  have ht0 : 0 < |κ / N| := by rw [hta]; exact div_pos hκa hN
  have hNs : 0 ≤ N ^ (-s) := Real.rpow_nonneg hN.le _
  constructor
  · have h := hC_val (κ / N) ht0 ht34
    have hpow : |κ / N| ^ (-s) = |κ| ^ (-s) * N ^ s := by
      rw [hta, Real.div_rpow hκa.le hN.le, Real.rpow_neg hN.le, div_inv_eq_mul]
    have hNN : N ^ (-s) * N ^ s = 1 := by
      rw [Real.rpow_neg hN.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hN _).ne']
    calc N ^ (-s) * |gradKernelH s (κ / N)|
        ≤ N ^ (-s) * (C₁ * |κ / N| ^ (-s)) := mul_le_mul_of_nonneg_left h hNs
      _ = C₁ * (|κ| ^ (-s) * N ^ s) * N ^ (-s) := by rw [hpow]; ring
      _ = C₁ * |κ| ^ (-s) := by
          rw [show C₁ * (|κ| ^ (-s) * N ^ s) * N ^ (-s) = C₁ * |κ| ^ (-s) * (N ^ (-s) * N ^ s) by ring,
            hNN, mul_one]
  · have h := hC_der (κ / N) ht0 ht34
    have hpow : |κ / N| ^ (-s - 1) = |κ| ^ (-s - 1) * N ^ (s + 1) := by
      rw [hta, Real.div_rpow hκa.le hN.le, show -s - 1 = -(s + 1) by ring,
        Real.rpow_neg hN.le, div_inv_eq_mul, show -(s + 1) = -s - 1 by ring]
    have hNN : N ^ (-s) * N ^ (s + 1) = N := by
      rw [← Real.rpow_add hN, show -s + (s + 1) = (1 : ℝ) by ring, Real.rpow_one]
    calc N ^ (-s) * |iteratedDeriv 1 (gradKernelH s) (κ / N)|
        ≤ N ^ (-s) * (C₁ * |κ / N| ^ (-s - 1)) := mul_le_mul_of_nonneg_left h hNs
      _ = C₁ * |κ| ^ (-s - 1) * (N ^ (-s) * N ^ (s + 1)) := by rw [hpow]; ring
      _ = C₁ * N * |κ| ^ (-s - 1) := by rw [hNN]; ring

/-- The final algebra of one pair: the three product estimates, with the rpow identities
`K^{s/2-1} K^{-s} = K^{-1-s/2}`, `K^{s/2} K^{-s-1} = K^{-1-s/2}` and `L, L² ≤ L^{s+2}` for
`L ≥ 1`, give the bound `C L^{s+2} K^{-1-s/2} S`. -/
lemma pair_final_algebra {s N c A Cp C₁ L Wu S κa : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hN : 0 < N)
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hCp : 0 ≤ Cp) (hC₁ : 0 ≤ C₁) (hL1 : 1 ≤ L) (hκa : 0 < κa)
    (hWu : 0 ≤ Wu) (hWuS : Wu ≤ S) :
    2 * (A * c * Wu) * (Cp * L ^ (s + 2) * κa ^ (-1 - s / 2))
      + 2 * (2 * A * c * (L * L * κa ^ (s / 2 - 1) * S)) * (C₁ * κa ^ (-s))
      + 2 * (A * c * (L * κa ^ (s / 2) / N) * S) * (C₁ * N * κa ^ (-s - 1))
      ≤ (2 * A * Cp + 6 * A * C₁) * c * L ^ (s + 2) * κa ^ (-1 - s / 2) * S := by
  have hLL : L * L ≤ L ^ (s + 2) := by
    have h1 : L ^ (2 : ℝ) ≤ L ^ (s + 2) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h2 : L ^ (2 : ℝ) = L * L := by rw [Real.rpow_two, sq]
    rw [← h2]
    exact h1
  have hLs : L ≤ L ^ (s + 2) := by
    have h1 : L ^ (1 : ℝ) ≤ L ^ (s + 2) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    rwa [Real.rpow_one] at h1
  have hp1 : κa ^ (s / 2 - 1) * κa ^ (-s) = κa ^ (-1 - s / 2) := by
    rw [← Real.rpow_add hκa]
    congr 1
    ring
  have hp2 : κa ^ (s / 2) * κa ^ (-s - 1) = κa ^ (-1 - s / 2) := by
    rw [← Real.rpow_add hκa]
    congr 1
    ring
  have hQ : 0 ≤ κa ^ (-1 - s / 2) := Real.rpow_nonneg hκa.le _
  have hP : 0 ≤ L ^ (s + 2) := Real.rpow_nonneg (by linarith) _
  have hS : 0 ≤ S := le_trans hWu hWuS
  have e1 : 2 * (A * c * Wu) * (Cp * L ^ (s + 2) * κa ^ (-1 - s / 2))
      = (2 * A * Cp * c * L ^ (s + 2) * κa ^ (-1 - s / 2)) * Wu := by ring
  have e2 : 2 * (2 * A * c * (L * L * κa ^ (s / 2 - 1) * S)) * (C₁ * κa ^ (-s))
      = (4 * A * C₁ * c * (L * L) * S) * (κa ^ (-1 - s / 2)) := by
    rw [← hp1]
    ring
  have e3 : 2 * (A * c * (L * κa ^ (s / 2) / N) * S) * (C₁ * N * κa ^ (-s - 1))
      = (2 * A * C₁ * c * L * S) * (κa ^ (-1 - s / 2)) := by
    rw [← hp2]
    field_simp
  rw [e1, e2, e3]
  have hK0 : 0 ≤ 2 * A * Cp * c * L ^ (s + 2) * κa ^ (-1 - s / 2) := by
    have : 0 ≤ 2 * A * Cp * c := by positivity
    exact mul_nonneg (mul_nonneg this hP) hQ
  have i1 : (2 * A * Cp * c * L ^ (s + 2) * κa ^ (-1 - s / 2)) * Wu
      ≤ (2 * A * Cp * c * L ^ (s + 2) * κa ^ (-1 - s / 2)) * S :=
    mul_le_mul_of_nonneg_left hWuS hK0
  have hco : 0 ≤ 4 * A * C₁ * c * S * κa ^ (-1 - s / 2) := by
    have : 0 ≤ 4 * A * C₁ * c * S := by positivity
    exact mul_nonneg this hQ
  have hco2 : 0 ≤ 2 * A * C₁ * c * S * κa ^ (-1 - s / 2) := by
    have : 0 ≤ 2 * A * C₁ * c * S := by positivity
    exact mul_nonneg this hQ
  have i2 : (4 * A * C₁ * c * (L * L) * S) * (κa ^ (-1 - s / 2))
      ≤ (4 * A * C₁ * c * S * L ^ (s + 2)) * (κa ^ (-1 - s / 2)) := by
    apply mul_le_mul_of_nonneg_right _ hQ
    have h := mul_le_mul_of_nonneg_left hLL (by positivity : (0 : ℝ) ≤ 4 * A * C₁ * c * S)
    linarith [h]
  have i3 : (2 * A * C₁ * c * L * S) * (κa ^ (-1 - s / 2))
      ≤ (2 * A * C₁ * c * S * L ^ (s + 2)) * (κa ^ (-1 - s / 2)) := by
    apply mul_le_mul_of_nonneg_right _ hQ
    have h := mul_le_mul_of_nonneg_left hLs (by positivity : (0 : ℝ) ≤ 2 * A * C₁ * c * S)
    linarith [h]
  linarith [i1, i2, i3]

/-- One pair of the displacement sum: `|2N^{-s}(Z_x(x,y) h(r) - Z_x(x,z) h(t)) - 2N^{-s}(Z(x,y) - Z(x,z)) h'(t)|`
with `x = x_i`, `y = x_i + r_{ij}`, `z = x_i + t`, `t = k_{ij}/N`, is at most
`C_E C0 ℓ^{-1} (K^ε)^{s+2} |k|^{-1-s/2} (w_2(x) + w_2(y) + w_2(z))`. -/
lemma gradV1_pair_bound {s α γ ε C₁ C0 ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {ψ : ℝ → ℝ}
    {i j : ℤ} (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) (hC0 : 0 ≤ C0)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (_hN : 2 ≤ (N : ℕ))
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ⁻¹)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t)
    (hC₁0 : 0 ≤ C₁)
    (hC_val : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 → |gradKernelH s u| ≤ C₁ * |u| ^ (-s))
    (hC_der : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 →
      |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * |u| ^ (-s - 1))
    (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8) (_hγ : 1 < γ)
    (hX : gradEvent s γ ε N ℓ X) (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ)
    (hne : j ≠ i) :
    |2 * ((N : ℕ) : ℝ) ^ (-s) * (gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * gradKernelH s (gradSep N ℓ γ X i j)
        - gradZx ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ))
          * gradKernelH s ((gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)))
      - 2 * ((N : ℕ) : ℝ) ^ (-s) * (gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          - gradZ ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)))
          * deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ))|
      ≤ (2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * (C0 * ℓ⁻¹)
        * (((((N : ℕ) : ℝ) * ℓ) ^ ε)) ^ (s + 2) * |(gradPathIncr N ℓ γ i j : ℝ)| ^ (-1 - s / 2)
        * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ)) := by
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := hN0.ne'
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hKN : ((N : ℕ) : ℝ) * ℓ ≤ ((N : ℕ) : ℝ) := by nlinarith
  have hα_a0 : 0 ≤ 1 - s + α := by linarith
  have hα_a1 : 1 - s + α < 1 := by linarith
  have hκ0 : (gradPathIncr N ℓ γ i j : ℝ) ≠ 0 := by
    exact_mod_cast gradPathIncr_ne_zero hi hj hne
  obtain ⟨hF2a, _, hDκ⟩ := gradSep_abs_bounds hK hX hi hj hne
  have hF1 := gradSep_event_bound hX hi hj hne
  have h2κ : 2 * |(gradPathIncr N ℓ γ i j : ℝ)| ≤ ((N : ℕ) : ℝ) := by
    have h := two_abs_gradPathIncr_le hi hj
    have h' : (2 : ℝ) * ((|(gradPathIncr N ℓ γ i j : ℤ)| : ℤ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Int.cast_abs] at h'
    exact h'
  have hC_der_pos : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 →
      |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * u ^ (-s - 1) := by
    intro u hu hu34
    have h := hC_der u (abs_pos.mpr hu.ne') (by rw [abs_of_pos hu]; exact hu34)
    rwa [abs_of_pos hu] at h
  have hD34 : (N : ℝ) < (4 : ℝ) ^ (2 / (1 - s / 2)) → |gradSep N ℓ γ X i j| ≤ 3 / 4 :=
    fun hNN => gradSep_abs_le_three_quarters hK
      (rpow_le_two_of_lt_threshold hs1 hε hεs hK0 hKN hNN) hX hi hj hne
  have hP1 := gradKernel_pair_bound hs0 hs1 hC₁0 hC_der_pos hC_val hK hKN hε hεs hN0 hκ0
    (by exact_mod_cast h2κ) hDκ hF2a hF1 hD34
  have ht34 : |(gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)| ≤ 3 / 4 := by
    rw [abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    linarith
  have hκa : 0 < |(gradPathIncr N ℓ γ i j : ℝ)| := abs_pos.mpr hκ0
  obtain ⟨hL1, hL2⟩ := kernel_lattice_bounds hs0 hC₁0 hN0 hκa ht34 hC_val hC_der
  -- abbreviate `λ = K^ε` as `lam`
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (((N : ℕ) : ℝ) * ℓ) ^ ε := ⟨_, rfl⟩
  have hlampos : 0 < lam := hlam ▸ Real.rpow_pos_of_pos hK0 _
  have hlam1 : 1 ≤ lam := hlam ▸ Real.one_le_rpow hK hε.le
  have hlaminv : (((N : ℕ) : ℝ) * ℓ) ^ (-ε) = lam⁻¹ := by
    rw [hlam, Real.rpow_neg hK0.le]
  rw [← hlam] at hF1 hP1
  rw [hlaminv] at hF2a
  rw [← iteratedDeriv_one]
  generalize hr : gradSep N ℓ γ X i j = r at *
  generalize hκ : (gradPathIncr N ℓ γ i j : ℝ) = κ at *
  generalize hx : gradLift N X i = x at *
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_mul] at hDκ
    exact lt_irrefl _ hDκ
  have hκa' : 0 < |κ| := abs_pos.mpr hκ0
  -- the three `Z` facts
  have hd_y : 0 < |x + r - x| := by
    rw [add_sub_cancel_left]
    exact abs_pos.mpr hr0
  have hd_z : 0 < |x + κ / ((N : ℕ) : ℝ) - x| := by
    rw [add_sub_cancel_left]
    exact abs_pos.mpr (div_ne_zero hκ0 hNne)
  have hZu := gradZx_abs_le (s := s) (a := 1 - s + α) (K := ((N : ℕ) : ℝ) * ℓ) hℓ hs0 hs1
    hα_a0 hα_a1 hK hC0 hψ hper hbd hbd2 hd_y
  have hZX := gradZx_sub_gradZx_le (s := s) (a := 1 - s + α) (K := ((N : ℕ) : ℝ) * ℓ) hℓ hs0 hs1
    hα_a0 hα_a1 hK hC0 hψ hper hbd hbd2 hd_y hd_z
  have hZZ := gradZ_sub_gradZ_le (s := s) (a := 1 - s + α) (K := ((N : ℕ) : ℝ) * ℓ) hℓ hs0 hs1
    hα_a0 hα_a1 hK hC0 hψ hper hbd hbd2 x (x + r) (x + κ / ((N : ℕ) : ℝ))
  have hzy : |x + κ / ((N : ℕ) : ℝ) - (x + r)| ≤ lam * |κ| ^ (s / 2) / ((N : ℕ) : ℝ) := by
    have e : x + κ / ((N : ℕ) : ℝ) - (x + r) = -(((N : ℕ) : ℝ) * r - κ) / ((N : ℕ) : ℝ) := by
      field_simp
      ring
    rw [e, abs_div, abs_neg, abs_of_pos hN0]
    exact div_le_div_of_nonneg_right hF1 hN0.le
  have hmpos : 0 < lam⁻¹ * (|κ| / ((N : ℕ) : ℝ)) :=
    mul_pos (inv_pos.mpr hlampos) (div_pos hκa' hN0)
  have hmin : lam⁻¹ * (|κ| / ((N : ℕ) : ℝ)) ≤ min |x + r - x| |x + κ / ((N : ℕ) : ℝ) - x| := by
    rw [add_sub_cancel_left, add_sub_cancel_left]
    apply le_min
    · have h1 : lam⁻¹ * (|κ| / ((N : ℕ) : ℝ)) ≤ |r| := by
        rw [← mul_div_assoc, div_le_iff₀ hN0]
        linarith [hF2a]
      exact h1
    · rw [abs_div, abs_of_pos hN0]
      exact mul_le_of_le_one_left (div_nonneg hκa'.le hN0.le) (inv_le_one_of_one_le₀ hlam1)
  have hratio : |x + κ / ((N : ℕ) : ℝ) - (x + r)| / min |x + r - x| |x + κ / ((N : ℕ) : ℝ) - x|
      ≤ lam * lam * |κ| ^ (s / 2 - 1) := by
    calc |x + κ / ((N : ℕ) : ℝ) - (x + r)| / min |x + r - x| |x + κ / ((N : ℕ) : ℝ) - x|
        ≤ |x + κ / ((N : ℕ) : ℝ) - (x + r)| / (lam⁻¹ * (|κ| / ((N : ℕ) : ℝ))) :=
          div_le_div_of_nonneg_left (abs_nonneg _) hmpos hmin
      _ ≤ (lam * |κ| ^ (s / 2) / ((N : ℕ) : ℝ)) / (lam⁻¹ * (|κ| / ((N : ℕ) : ℝ))) :=
          div_le_div_of_nonneg_right hzy hmpos.le
      _ = lam * lam * |κ| ^ (s / 2 - 1) := by
          rw [Real.rpow_sub_one hκa'.ne']
          field_simp
  -- the three product estimates
  have hA0 : 0 ≤ gradZConst (1 - s + α) s + 1 := by
    have := gradZConst_nonneg (a := 1 - s + α) (s := s) (by linarith) hs1
    linarith
  have hc0 : 0 ≤ C0 * ℓ⁻¹ := mul_nonneg hC0 (inv_nonneg.mpr hℓ.le)
  have hWx := gradWeightTwo_nonneg_unconditional s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
  have hWy := gradWeightTwo_nonneg_unconditional s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
    ((x + r) / ℓ)
  have hWz := gradWeightTwo_nonneg_unconditional s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
    ((x + κ / ((N : ℕ) : ℝ)) / ℓ)
  have hWu0 : 0 ≤ gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
      + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ) := by linarith
  have hWuS : gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
      + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
      ≤ gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
        + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
        + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ) := by
    linarith
  have hn0 : 0 ≤ ((N : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg hN0.le _
  -- bound on `|Z_x(x,y)|`
  have hu : |gradZx ψ ℓ x (x + r)| ≤ (gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹)
      * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
        + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)) := by
    calc |gradZx ψ ℓ x (x + r)| ≤ (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹
          * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)) := hZu
      _ = _ := by ring
  -- bound on `|Z_x(x,y) - Z_x(x,z)|`
  have hdiffX : |gradZx ψ ℓ x (x + r) - gradZx ψ ℓ x (x + κ / ((N : ℕ) : ℝ))|
      ≤ 2 * ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹)
        * (lam * lam * |κ| ^ (s / 2 - 1))
        * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ))) := by
    have hcoef2 : 0 ≤ 2 * (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) hC0) (inv_nonneg.mpr hℓ.le)
    have hS' : 0 ≤ gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
        + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
        + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ) := by
      linarith
    have h1 := mul_le_mul_of_nonneg_left hratio hcoef2
    have h2 := mul_le_mul_of_nonneg_right h1 hS'
    calc |gradZx ψ ℓ x (x + r) - gradZx ψ ℓ x (x + κ / ((N : ℕ) : ℝ))|
        = |gradZx ψ ℓ x (x + κ / ((N : ℕ) : ℝ)) - gradZx ψ ℓ x (x + r)| := abs_sub_comm _ _
      _ ≤ 2 * (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹
            * |x + κ / ((N : ℕ) : ℝ) - (x + r)| / min |x + r - x| |x + κ / ((N : ℕ) : ℝ) - x|
            * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)) :=
          hZX
      _ = (2 * (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹)
            * (|x + κ / ((N : ℕ) : ℝ) - (x + r)| / min |x + r - x| |x + κ / ((N : ℕ) : ℝ) - x|)
            * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)) := by
          ring
      _ ≤ (2 * (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹) * (lam * lam * |κ| ^ (s / 2 - 1))
            * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)) :=
          h2
      _ = 2 * ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹)
            * (lam * lam * |κ| ^ (s / 2 - 1))
            * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ))) := by
          ring
  have hdiffZ : |gradZ ψ ℓ x (x + r) - gradZ ψ ℓ x (x + κ / ((N : ℕ) : ℝ))|
      ≤ (gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹) * (lam * |κ| ^ (s / 2) / ((N : ℕ) : ℝ))
        * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)) := by
    have hcoefA : 0 ≤ (gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹) :=
      mul_nonneg hA0 hc0
    have hS' : 0 ≤ gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
        + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
        + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ) := by
      linarith
    have h1 := mul_le_mul_of_nonneg_left hzy hcoefA
    have h2 := mul_le_mul_of_nonneg_right h1 hS'
    calc |gradZ ψ ℓ x (x + r) - gradZ ψ ℓ x (x + κ / ((N : ℕ) : ℝ))|
        = |gradZ ψ ℓ x (x + κ / ((N : ℕ) : ℝ)) - gradZ ψ ℓ x (x + r)| := abs_sub_comm _ _
      _ ≤ (gradZConst (1 - s + α) s + 1) * C0 * ℓ⁻¹ * |x + κ / ((N : ℕ) : ℝ) - (x + r)|
            * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)) :=
          hZZ
      _ = ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹)) * |x + κ / ((N : ℕ) : ℝ) - (x + r)|
            * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)) := by
          ring
      _ ≤ ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹)) * (lam * |κ| ^ (s / 2) / ((N : ℕ) : ℝ))
            * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)) :=
          h2
      _ = (gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹) * (lam * |κ| ^ (s / 2) / ((N : ℕ) : ℝ))
            * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
              + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)) := by
          ring
  -- the three products with the kernel bounds
  have hS'' : 0 ≤ gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
      + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
      + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ) := by
    linarith
  have hT1 : |gradZx ψ ℓ x (x + r)| * (((N : ℕ) : ℝ) ^ (-s) * |gradKernelH s r - gradKernelH s (κ / ((N : ℕ) : ℝ))|)
      ≤ ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹)
          * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)))
        * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) * lam ^ (s + 2)
            * |κ| ^ (-1 - s / 2)) :=
    mul_le_mul hu (by linarith [hP1]) (mul_nonneg hn0 (abs_nonneg _))
      (mul_nonneg (mul_nonneg hA0 hc0) hWu0)
  have hq2 : 0 ≤ 2 * ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹) * (lam * lam * |κ| ^ (s / 2 - 1))
      * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
        + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
        + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ))) := by
    have hpow : 0 ≤ lam * lam * |κ| ^ (s / 2 - 1) :=
      mul_nonneg (mul_nonneg hlampos.le hlampos.le) (Real.rpow_nonneg (abs_nonneg _) _)
    exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg hA0 hc0) hpow) hS'')
  have hT2 : |gradZx ψ ℓ x (x + r) - gradZx ψ ℓ x (x + κ / ((N : ℕ) : ℝ))|
      * (((N : ℕ) : ℝ) ^ (-s) * |gradKernelH s (κ / ((N : ℕ) : ℝ))|)
      ≤ (2 * ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹) * (lam * lam * |κ| ^ (s / 2 - 1))
          * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ))))
        * (C₁ * |κ| ^ (-s)) :=
    mul_le_mul hdiffX hL1 (mul_nonneg hn0 (abs_nonneg _)) hq2
  have hT3 : |gradZ ψ ℓ x (x + r) - gradZ ψ ℓ x (x + κ / ((N : ℕ) : ℝ))|
      * (((N : ℕ) : ℝ) ^ (-s) * |iteratedDeriv 1 (gradKernelH s) (κ / ((N : ℕ) : ℝ))|)
      ≤ ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹) * (lam * |κ| ^ (s / 2) / ((N : ℕ) : ℝ))
          * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)))
        * (C₁ * ((N : ℕ) : ℝ) * |κ| ^ (-s - 1)) :=
    mul_le_mul hdiffZ hL2 (mul_nonneg hn0 (abs_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg hA0 hc0)
        (div_nonneg (mul_nonneg hlampos.le (Real.rpow_nonneg (abs_nonneg _) _)) hN0.le)) hS'')
  have hCp0 : 0 ≤ C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) :=
    mul_nonneg (mul_nonneg hC₁0 (by positivity))
      (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
  have hsplit := V1_pair_split (n := ((N : ℕ) : ℝ) ^ (-s)) (u := gradZx ψ ℓ x (x + r))
    (v := gradZx ψ ℓ x (x + κ / ((N : ℕ) : ℝ))) (p := gradZ ψ ℓ x (x + r))
    (q := gradZ ψ ℓ x (x + κ / ((N : ℕ) : ℝ))) (H1 := gradKernelH s r)
    (H0 := gradKernelH s (κ / ((N : ℕ) : ℝ)))
    (Hp := iteratedDeriv 1 (gradKernelH s) (κ / ((N : ℕ) : ℝ))) hn0
  rw [← hlam]
  calc _ ≤ 2 * (|gradZx ψ ℓ x (x + r)| * (((N : ℕ) : ℝ) ^ (-s)
          * |gradKernelH s r - gradKernelH s (κ / ((N : ℕ) : ℝ))|))
        + 2 * (|gradZx ψ ℓ x (x + r) - gradZx ψ ℓ x (x + κ / ((N : ℕ) : ℝ))|
          * (((N : ℕ) : ℝ) ^ (-s) * |gradKernelH s (κ / ((N : ℕ) : ℝ))|))
        + 2 * (|gradZ ψ ℓ x (x + r) - gradZ ψ ℓ x (x + κ / ((N : ℕ) : ℝ))|
          * (((N : ℕ) : ℝ) ^ (-s) * |iteratedDeriv 1 (gradKernelH s) (κ / ((N : ℕ) : ℝ))|)) :=
        hsplit
    _ ≤ 2 * ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹) * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)))
          * ((C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2)) * lam ^ (s + 2)
            * |κ| ^ (-1 - s / 2))
        + 2 * (2 * (gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹) * (lam * lam * |κ| ^ (s / 2 - 1) * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ))))
          * (C₁ * |κ| ^ (-s))
        + 2 * ((gradZConst (1 - s + α) s + 1) * (C0 * ℓ⁻¹) * (lam * |κ| ^ (s / 2) / ((N : ℕ) : ℝ)) * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)))
          * (C₁ * ((N : ℕ) : ℝ) * |κ| ^ (-s - 1)) := by
        linarith [hT1, hT2, hT3]
    _ ≤ (2 * (gradZConst (1 - s + α) s + 1) * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * (C0 * ℓ⁻¹) * lam ^ (s + 2) * |κ| ^ (-1 - s / 2)
          * (gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + r) / ℓ)
            + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ ((x + κ / ((N : ℕ) : ℝ)) / ℓ)) :=
        pair_final_algebra hs0 hs1 hN0 hc0 hA0 hCp0 hC₁0 hlam1 hκa' hWu0 hWuS
    _ = _ := by ring

end

end Riesz1
