/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingCellsBounds

/-!
# One-cell quadrature of the gradient splitting

Part of Lemma 5.7, with the definitions
of `F_x` and `R_x` (`GradientSplittingCellsDefs.lean`).

The main theorem `Riesz1.gradient_splitting_cells` states the identity `F_x = -N^{-s} ψ'(x/ℓ) h' + R_x`
and the four bounds of the lemma, with one constant `C = C(s, α)`. The fourth bound, on the
difference between `R_x(k)` and the average of `R_x` over the cell `[k - 1/2, k + 1/2]`, is
`gradCell_cell_difference`. Its proof uses only the derivative of `R_x` and no finite-difference
claim of the differences part of Lemma 5.7.

The constant `C` depends on `s` and `α` only, through the constants of the lemmas
`gradSplit_derivative_bounds` and `gradSplit_differences_bounds`.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- A point with `0 < |v| < N` lies in `gradCellSet N`. -/
lemma mem_gradCellSet_of_lt {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv0 : 0 < |v|) (hv : |v| < N) :
    v ∈ gradCellSet N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hr : v / (N : ℝ) ≠ 0 := div_ne_zero (abs_pos.mp hv0) hNpos.ne'
  have h1 : |v / (N : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos hNpos, div_lt_one hNpos]
    exact hv
  show ((v / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0
  exact gradSplit_coe_ne_zero (abs_pos.mpr hr) h1

/-- A point with `0 < |v| ≤ 3N/4` lies in `gradCellSet N`. -/
lemma mem_gradCellSet_of_le {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv0 : 0 < |v|) (hv : |v| ≤ 3 * N / 4) :
    v ∈ gradCellSet N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hr : v / (N : ℝ) ≠ 0 := div_ne_zero (abs_pos.mp hv0) hNpos.ne'
  have h1 : |v / (N : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos hNpos, div_lt_one hNpos]
    linarith
  show ((v / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0
  exact gradSplit_coe_ne_zero (abs_pos.mpr hr) h1

/-- The fourth bound of the cell part of Lemma 5.7: for an integer `k` with `0 < |k| ≤ N/2`,
the value `R_x(k)` differs from the average of `R_x` over the cell `[k - 1/2, k + 1/2]` by at most
the integral of `|R_x'|` over that cell. The derivative `R_x'` is continuous on the cell, since the
cell avoids the multiples of `N`. -/
lemma gradCell_cell_difference {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 ≤ N) (x : ℝ) (k : ℤ)
    (hk0 : 0 < |(k : ℝ)|) (hkN : |(k : ℝ)| ≤ N / 2) :
    |gradCellR s N ℓ ψ x k - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), gradCellR s N ℓ ψ x v| ≤
      ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s N ℓ ψ x) v| := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hkne : k ≠ 0 := by
    rintro rfl
    simp at hk0
  have hkcases : (1 : ℝ) ≤ k ∨ (k : ℝ) ≤ -1 := by
    rcases (show (1 : ℤ) ≤ k ∨ k ≤ -1 by omega) with h | h
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h
  have hab : (k : ℝ) - 1 / 2 ≤ (k : ℝ) + 1 / 2 := by linarith
  have hkI : (k : ℝ) ∈ uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := by
    rw [uIcc_of_le hab]
    constructor <;> linarith
  -- Every point of the cell has `0 < |t| ≤ 3N/4`, hence lies in `gradCellSet N`.
  have hcell : uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) ⊆ gradCellSet N := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hkabs : |(k : ℝ)| ≤ N / 2 := hkN
    have hpos : 0 < |t| := by
      rw [abs_pos]
      rcases hkcases with h | h
      · intro h0; linarith [ht.1]
      · intro h0; linarith [ht.2]
    have hle : |t| ≤ 3 * N / 4 := by
      rw [abs_le]
      have hk' := abs_le.mp hkabs
      constructor <;> linarith [ht.1, ht.2, hk'.1, hk'.2]
    exact mem_gradCellSet_of_le hN hpos hle
  have hRC : ContDiffOn ℝ ∞ (gradCellR s N ℓ ψ x) (gradCellSet N) :=
    contDiffOn_gradCellR hs0 hs1 hψ hℓ N x
  have hdRC : ContDiffOn ℝ ∞ (deriv (gradCellR s N ℓ ψ x)) (gradCellSet N) :=
    hRC.deriv_of_isOpen (gradCellSet_isOpen N) (by simp)
  have hcR : ContinuousOn (gradCellR s N ℓ ψ x) (uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
    hRC.continuousOn.mono hcell
  have hcD : ContinuousOn (deriv (gradCellR s N ℓ ψ x))
      (uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
    hdRC.continuousOn.mono hcell
  have hIR : IntervalIntegrable (gradCellR s N ℓ ψ x) volume
      ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := hcR.intervalIntegrable
  have hID : IntervalIntegrable (fun t => ‖deriv (gradCellR s N ℓ ψ x) t‖) volume
      ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) :=
    hcD.norm.intervalIntegrable
  have hIoc : IntegrableOn (fun t => ‖deriv (gradCellR s N ℓ ψ x) t‖)
      (uIoc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) volume := by
    rw [uIoc_of_le hab]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hID
  -- The fundamental theorem of calculus on the segment from `v` to `k`.
  have hd : ∀ t ∈ uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
      HasDerivAt (gradCellR s N ℓ ψ x) (deriv (gradCellR s N ℓ ψ x) t) t := by
    intro t ht
    exact ((hRC.differentiableOn (by simp)).differentiableAt
      ((gradCellSet_isOpen N).mem_nhds (hcell ht))).hasDerivAt
  have hstep : ∀ v ∈ uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
      ‖gradCellR s N ℓ ψ x k - gradCellR s N ℓ ψ x v‖ ≤
        ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s N ℓ ψ x) t| := by
    intro v hv
    have hsub : uIcc v (k : ℝ) ⊆ uIcc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) :=
      Set.uIcc_subset_uIcc hv hkI
    have hFTC : ∫ t in v..(k : ℝ), deriv (gradCellR s N ℓ ψ x) t =
        gradCellR s N ℓ ψ x k - gradCellR s N ℓ ψ x v :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub ht))
        (hcD.mono hsub).intervalIntegrable
    have hsubI : uIoc v (k : ℝ) ⊆ uIoc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) :=
      Set.uIoc_subset_uIoc_of_uIcc_subset_uIcc hsub
    calc ‖gradCellR s N ℓ ψ x k - gradCellR s N ℓ ψ x v‖
        = ‖∫ t in v..(k : ℝ), deriv (gradCellR s N ℓ ψ x) t‖ := by rw [hFTC]
      _ ≤ ∫ t in uIoc v (k : ℝ), ‖deriv (gradCellR s N ℓ ψ x) t‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ t in uIoc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), ‖deriv (gradCellR s N ℓ ψ x) t‖ :=
          setIntegral_mono_set hIoc (ae_of_all _ fun t => norm_nonneg _)
            (ae_of_all _ fun t ht => hsubI ht)
      _ = ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s N ℓ ψ x) t| := by
          rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
          simp only [Real.norm_eq_abs]
  have hba : (k : ℝ) + 1 / 2 - ((k : ℝ) - 1 / 2) = 1 := by ring
  have hint_eq : ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
      (gradCellR s N ℓ ψ x k - gradCellR s N ℓ ψ x v) =
        gradCellR s N ℓ ψ x k - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
          gradCellR s N ℓ ψ x v := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hIR, intervalIntegral.integral_const,
      hba, one_smul]
  calc |gradCellR s N ℓ ψ x k - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
          gradCellR s N ℓ ψ x v|
      = ‖∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
          (gradCellR s N ℓ ψ x k - gradCellR s N ℓ ψ x v)‖ := by
        rw [hint_eq, Real.norm_eq_abs]
    _ ≤ (∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s N ℓ ψ x) t|) *
          |(k : ℝ) + 1 / 2 - ((k : ℝ) - 1 / 2)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun v hv =>
          hstep v (Set.uIoc_subset_uIcc hv))
    _ = ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s N ℓ ψ x) t| := by
        rw [hba, abs_one, mul_one]

/-- The cell part of Lemma 5.7, with the definitions of `F_x` and `R_x`.
For `0 < s < 1` and `s - 1 ≤ α < s/2`, there is `C = C(s, α) > 0` such that for every integer
`N ≥ 2`, every `0 < ℓ ≤ 1` with `K = Nℓ ≥ 1`, every `C_0 ≥ 0`, every real `x`, and every smooth
`ℓ^{-1}`-periodic `ψ` with `|ψ'| ≤ C_0 w_1` and `|ψ''| ≤ C_0 w_2`:

* the identity `F_x(v) = -N^{-s} ψ'(x/ℓ) h'(v/N) + R_x(v)` holds for `0 < |v| < N`.
* `|R_x(v)| ≤ C C_0 ℓ^{-1} (w_2(x/ℓ) + w_2((x+v/N)/ℓ)) |v|^{-s}` for `0 < |v| ≤ 3N/4`, which
  contains the range `0 < |v| < 1/2`.
* `|R_x'(v)| ≤ C C_0 ℓ^{-1} (w_2(x/ℓ) + w_2((x+v/N)/ℓ)) |v|^{-1-s}` for `1/2 ≤ |v| ≤ 3N/4`.
* `R_x` is interval integrable on `[-1/2, 1/2]` and `∫_{-1/2}^{1/2} |R_x| ≤ C C_0 ℓ^{-1} w_2(x/ℓ)`.
* for every integer `k` with `0 < |k| ≤ N/2`, the difference between `R_x(k)` and the average of
  `R_x` over `[k - 1/2, k + 1/2]` is at most the integral of `|R_x'|` over that cell.

The first bound is stated on `0 < |v| ≤ 3N/4` rather than `0 < |v| < N`. On `3N/4 < |v| < N` the
bound fails: as `v/N → 1`, `R_x(v)` blows up like `ψ'(x/ℓ) (1 - v/N)^{-2-s}` while the right side
stays bounded. -/
theorem gradient_splitting_cells {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α)
    (hα1 : α < s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (ℓ C0 x : ℝ) (ψ : ℝ → ℝ),
      2 ≤ N → 0 < ℓ → ℓ ≤ 1 → 1 ≤ N * ℓ → 0 ≤ C0 → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) (N * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ t) →
      (∀ v : ℝ, 0 < |v| → |v| < N →
        gradCellF s N ℓ ψ x v = -(N : ℝ) ^ (-s) * deriv ψ (x / ℓ) *
          iteratedDeriv 1 (gradKernelH s) (v / N) + gradCellR s N ℓ ψ x v) ∧
      (∀ v : ℝ, 0 < |v| → |v| ≤ 3 * N / 4 →
        |gradCellR s N ℓ ψ x v| ≤ C * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) * |v| ^ (-s)) ∧
      (∀ v : ℝ, 1 / 2 ≤ |v| → |v| ≤ 3 * N / 4 →
        |deriv (gradCellR s N ℓ ψ x) v| ≤ C * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) * |v| ^ (-1 - s)) ∧
      IntervalIntegrable (gradCellR s N ℓ ψ x) volume (-(1 / 2)) (1 / 2) ∧
      (∫ v in (-(1 / 2))..(1 / 2), |gradCellR s N ℓ ψ x v| ≤
        C * C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ)) ∧
      (∀ k : ℤ, 0 < |(k : ℝ)| → |(k : ℝ)| ≤ N / 2 →
        |gradCellR s N ℓ ψ x k - ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
            gradCellR s N ℓ ψ x v| ≤
          ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), |deriv (gradCellR s N ℓ ψ x) v|) := by
  obtain ⟨Cg, hCg0, hg⟩ := gradSplit_derivative_bounds s hs0 hs1
  obtain ⟨Cd, hCd0, hdiff⟩ := gradSplit_differences_bounds hs0 hs1 hα0 hα1
  have ha0 : 0 ≤ 1 - s + α := by linarith
  have h1s : 0 < 1 - s := by linarith
  -- The constant: `A = 1 + 64·2^a`, `I = 2(1/2)^{1-s}/(1-s)`, `F = 4 A (1 + I)`.
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 + 64 * (2 : ℝ) ^ (1 - s + α) := ⟨_, rfl⟩
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = 2 * (1 / 2 : ℝ) ^ (1 - s) / (1 - s) := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 - s + α)
    linarith
  have hA0 : 0 ≤ A := by linarith
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) h1s.le
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = 4 * A * (1 + I) := ⟨_, rfl⟩
  have hF1 : 1 ≤ F := by
    rw [hFdef]
    nlinarith [mul_nonneg (sub_nonneg.mpr hA1) hI0]
  have hF4 : 4 ≤ F := by
    rw [hFdef]
    nlinarith [mul_nonneg (sub_nonneg.mpr hA1) hI0]
  have hFI : A * I ≤ F := by
    rw [hFdef]
    nlinarith [mul_nonneg hA0 hI0]
  have hKpos : 0 < Cd * Cg := mul_pos hCd0 hCg0
  refine ⟨F * (Cd * Cg), mul_pos (by linarith) hKpos, ?_⟩
  intro N ℓ C0 x ψ hN hℓ hℓ1 hK hC0 hψ hper hbd hbd2
  have hℓi : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
  obtain ⟨-, -, hZsum, hZxy⟩ := hdiff N ℓ C0 ψ hN hℓ hℓ1 hK hC0 hψ hper hbd hbd2
  have hZ : ∀ y : ℝ, 0 < |y - x| → |gradZx ψ ℓ x y| ≤ Cd * C0 * ℓ⁻¹ *
      (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ)) := by
    intro y hy
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hZsum x y hy)
  have hg2 : ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 →
      |iteratedDeriv 2 (hurwitzKernel s) r| ≤ Cg * |r| ^ (-s - 2) := by
    intro r h0 h1
    have h := (hg r h0 h1).1 2 (by norm_num) (by norm_num)
    have e : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rwa [e] at h
  have hg3 : ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 →
      |iteratedDeriv 3 (hurwitzKernel s) r| ≤ Cg * |r| ^ (-s - 3) := by
    intro r h0 h1
    have h := (hg r h0 h1).1 3 (by norm_num) (by norm_num)
    have e : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rwa [e] at h
  have hW : ∀ y : ℝ, 0 ≤ gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (y / ℓ) :=
    fun y => gradCell_w2_nonneg _ _ _ _ _
  have hK' : 1 ≤ (N : ℝ) * ℓ := hK
  have hKpos' : 0 ≤ Cd * Cg := hKpos.le
  refine ⟨fun v hv0 hvN => gradCellF_eq hs0 hs1 N x (mem_gradCellSet_of_lt hN hv0 hvN), ?_, ?_,
    gradCellR_intervalIntegrable hs0 hs1 ha0 hψ hℓ N hN hK' x hC0 hCd0.le hCg0.le hZ hg2, ?_, ?_⟩
  · -- The first bound, on `0 < |v| ≤ 3N/4`.
    intro v hv0 hv2
    have hv0' : v ≠ 0 := fun h => by simp [h] at hv0
    have hp := gradCellR_bound_pointwise hs0 hs1 hℓ N hN x hv0' hv2 hC0 hCd0.le hZ hg2
    have hP : 0 ≤ C0 * ℓ⁻¹ * (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) :=
      mul_nonneg (mul_nonneg hC0 hℓi) (add_nonneg (hW _) (hW _))
    have hrp : 0 ≤ |v| ^ (-s) := Real.rpow_nonneg (abs_nonneg v) _
    calc |gradCellR s N ℓ ψ x v|
        ≤ Cd * Cg * (C0 * ℓ⁻¹ * (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v| ^ (-s) := hp
      _ ≤ F * (Cd * Cg) * (C0 * ℓ⁻¹ * (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v| ^ (-s) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hKpos' hF1) hP) hrp
      _ = F * (Cd * Cg) * C0 * ℓ⁻¹ * (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) * |v| ^ (-s) := by
          ring
  · -- The second bound, on `1/2 ≤ |v| ≤ 3N/4`.
    intro v hv1 hv2
    have hmem : v ∈ gradCellSet N := mem_gradCellSet_of_le hN (by linarith) hv2
    have hd := gradCellR_deriv_bound hs0 hs1 hψ hℓ N hN x hmem hv2 hC0 hCd0.le hW hZ
      (fun y hy => hZxy x y hy)
      hg2 hg3
    have hP : 0 ≤ C0 * ℓ⁻¹ * (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) :=
      mul_nonneg (mul_nonneg hC0 hℓi) (add_nonneg (hW _) (hW _))
    have hrp : 0 ≤ |v| ^ (-1 - s) := Real.rpow_nonneg (abs_nonneg v) _
    calc |deriv (gradCellR s N ℓ ψ x) v|
        ≤ 4 * Cd * Cg * (C0 * ℓ⁻¹ * (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v| ^ (-1 - s) := hd
      _ ≤ F * (Cd * Cg) * (C0 * ℓ⁻¹ * (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v| ^ (-1 - s) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (by nlinarith [mul_nonneg hKpos' (sub_nonneg.mpr hF4)]) hP) hrp
      _ = F * (Cd * Cg) * C0 * ℓ⁻¹ * (gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) * |v| ^ (-1 - s) := by
          ring
  · -- The integral bound.
    have h3 := gradCellR_integral_le hs0 hs1 ha0 hψ hℓ N hN hK' x hC0 hCd0.le hCg0.le hZ hg2
    rw [← hAdef, ← hIdef] at h3
    have hP : 0 ≤ (Cd * Cg) * (C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ)) :=
      mul_nonneg hKpos' (mul_nonneg (mul_nonneg hC0 hℓi) (hW _))
    calc _ ≤ _ := h3
      _ = (Cd * Cg) * (C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ)) * (A * I) := by
          ring
      _ ≤ (Cd * Cg) * (C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ)) * F :=
          mul_le_mul_of_nonneg_left hFI hP
      _ = F * (Cd * Cg) * C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) (N * ℓ) ℓ⁻¹ (x / ℓ) := by
          ring
  · -- The fourth bound, on the cells `[k - 1/2, k + 1/2]` with `0 < |k| ≤ N/2`.
    intro k hk0 hkN
    exact gradCell_cell_difference hs0 hs1 hψ hℓ N hN x k hk0 hkN

end Riesz1

end
