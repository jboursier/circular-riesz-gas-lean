/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadraturePartialRemainder
public import Riesz1.Auxiliary.GradientSplittingQuadratureOdd
public import Riesz1.Auxiliary.GradientSplittingQuadraturePartialReduce

/-!
# Crude partial-window quadrature bounds

The quadrature part of Lemma 5.7, bounded-scale argument. Uniform
suprema of the envelopes and integrability of `|v|^(-s)` control the remainder.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The number of labels in a partial window is at most `3M`. -/
lemma gradQuad_partial_card_le {N : ℕ+} {ℓ γ : ℝ} (hP : GradPartial N ℓ γ)
    (hM : 1 ≤ gradM N ℓ γ) (i : ℤ) :
    (((gradLabels N ℓ γ).erase i).card : ℝ) ≤ 3 * gradM N ℓ γ := by
  have hn : (0 : ℤ) ≤ ⌊gradM N ℓ γ⌋ := Int.floor_nonneg.mpr (by linarith)
  have hc : ((gradLabels N ℓ γ).card : ℝ) = 2 * (⌊gradM N ℓ γ⌋ : ℝ) + 1 := by
    simp only [gradLabels, hP, ↓reduceIte, Int.card_Icc]
    exact_mod_cast (show (((⌊gradM N ℓ γ⌋ + 1 - -⌊gradM N ℓ γ⌋).toNat : ℕ) : ℤ) =
        2 * ⌊gradM N ℓ γ⌋ + 1 from by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ ⌊gradM N ℓ γ⌋ + 1 - -⌊gradM N ℓ γ⌋)]
      ring)
  have he : (((gradLabels N ℓ γ).erase i).card : ℝ) ≤ ((gradLabels N ℓ γ).card : ℝ) := by
    exact_mod_cast (Finset.card_erase_le : ((gradLabels N ℓ γ).erase i).card ≤ (gradLabels N ℓ γ).card)
  linarith [Int.floor_le (gradM N ℓ γ)]

/-- A crude bound for the sum and background integral of the remainder when `M ≤ H`.
The constant is chosen before the scale and configuration. -/
theorem gradQuad_remainder_crude {s α H : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) (hH : 1 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ C0 x : ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → GradPartial N ℓ γ →
      gradM N ℓ γ ≤ H → |(N : ℝ) * x| ≤ 3 * gradM N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      i ∈ gradLabels N ℓ γ →
      |(∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradCellR s (N : ℕ) ℓ ψ x (gradPathIncr N ℓ γ i j)) -
        ∫ v in (-gradM N ℓ γ - (N : ℝ) * x)..(gradM N ℓ γ - (N : ℝ) * x),
          gradCellR s (N : ℕ) ℓ ψ x v|
        ≤ C * C0 * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) := by
  obtain ⟨Cc, hCc, hcells⟩ := gradient_splitting_cells hs0 hs1 hα0 hα1
  refine ⟨2 * Cc * (3 * H + 2 * (4 * H) ^ (1 - s) / (1 - s)), by positivity, ?_⟩
  intro N ℓ γ C0 x ψ i hN hℓ hℓ1 hK hγ hP hMH hx hC0 hψ hper h1 h2 hi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hKpos : 0 < (N : ℝ) * ℓ := by linarith
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  let R := gradCellR s (N : ℕ) ℓ ψ x
  let D := 2 * Cc * C0 * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint : ∀ v : ℝ, 0 < |v| → |v| ≤ 3 * (N : ℝ) / 4 → |R v| ≤ D * |v| ^ (-s) := by
    intro v hv0 hvN
    have hp := (hcells (N : ℕ) ℓ C0 x ψ hN hℓ hℓ1 hK hC0 hψ hper h1 h2).2.1 v hv0 hvN
    have hw (z : ℝ) : gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ z ≤
        ((N : ℝ) * ℓ) ^ (1 + (1 - s + α)) :=
      gradWeightTwo_le_K_pow hs1 (by linarith) hK
    have heq : ℓ⁻¹ * ((N : ℝ) * ℓ) ^ (1 + (1 - s + α)) =
        (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) := by
      rw [Real.rpow_add hKpos, Real.rpow_one]; field_simp
    calc
      _ ≤ Cc * C0 * ℓ⁻¹ *
        (((N : ℝ) * ℓ) ^ (1 + (1 - s + α)) + ((N : ℝ) * ℓ) ^ (1 + (1 - s + α))) *
          |v| ^ (-s) := hp.trans (by gcongr; exact hw _; exact hw _)
      _ = 2 * Cc * C0 * (ℓ⁻¹ * ((N : ℝ) * ℓ) ^ (1 + (1 - s + α))) * |v| ^ (-s) := by ring
      _ = _ := by rw [heq]; dsimp [D]; ring
  have hsum : |∑ j ∈ (gradLabels N ℓ γ).erase i, R (gradPathIncr N ℓ γ i j)| ≤ D * (3 * H) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ j ∈ (gradLabels N ℓ γ).erase i, D := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hne, hjl⟩ := Finset.mem_erase.mp hj
        have hk0 : 1 ≤ |(gradPathIncr N ℓ γ i j : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (gradPathIncr_ne_zero hi hjl hne)
        have hkN : |(gradPathIncr N ℓ γ i j : ℝ)| ≤ (N : ℝ) / 2 := by
          have hb : (2 : ℝ) * |(gradPathIncr N ℓ γ i j : ℝ)| ≤ (N : ℝ) := by
            exact_mod_cast two_abs_gradPathIncr_le hi hjl
          linarith
        exact (hpoint _ (by linarith) (by linarith)).trans
          (mul_le_of_le_one_right hD (Real.rpow_le_one_of_one_le_of_nonpos hk0 (by linarith)))
      _ = (((gradLabels N ℓ γ).erase i).card : ℝ) * D := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (gradQuad_partial_card_le hP hM i) hD]
  let a := -gradM N ℓ γ - (N : ℝ) * x
  let b := gradM N ℓ γ - (N : ℝ) * x
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hr0 := gradPartial_background_range hP hx (left_mem_Icc.mpr hab)
  have hr1 := gradPartial_background_range hP hx (right_mem_Icc.mpr hab)
  have hpower := intervalIntegrable_abs_rpow_symm hs1 (by linarith : 0 ≤ 4 * H)
  have hpowerbg := hpower.mono_set (uIcc_subset_uIcc
    (show a ∈ uIcc (-(4 * H)) (4 * H) by
      rw [uIcc_of_le (by linarith : -(4 * H) ≤ 4 * H)]; exact ⟨by linarith [(abs_le.mp hr0.1).1], by linarith [(abs_le.mp hr0.1).2]⟩)
    (show b ∈ uIcc (-(4 * H)) (4 * H) by
      rw [uIcc_of_le (by linarith : -(4 * H) ≤ 4 * H)]; exact ⟨by linarith [(abs_le.mp hr1.1).1], by linarith [(abs_le.mp hr1.1).2]⟩))
  have hnorm : |∫ v in a..b, R v| ≤ ∫ v in a..b, D * |v| ^ (-s) := by
    have hae : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 0 := by rw [ae_iff]; simp
    have hh := intervalIntegral.norm_integral_le_of_norm_le hab (μ := volume) (f := R)
      (g := fun v : ℝ => D * |v| ^ (-s)) (by
        filter_upwards [hae] with v hv hvI
        have hvr := gradPartial_background_range hP hx (Ioc_subset_Icc_self hvI)
        simpa only [Real.norm_eq_abs] using hpoint v (abs_pos.mpr hv) (by linarith [hvr.2]))
      (hpowerbg.const_mul D)
    simpa only [Real.norm_eq_abs] using hh
  have hint : (∫ v in a..b, |v| ^ (-s)) ≤ 2 * (4 * H) ^ (1 - s) / (1 - s) := by
    have hh := intervalIntegral.integral_mono_interval (μ := volume)
      (f := fun v : ℝ => |v| ^ (-s))
      (show -(4 * H) ≤ a by linarith [(abs_le.mp hr0.1).1]) hab
      (show b ≤ 4 * H by linarith [(abs_le.mp hr1.1).2])
      (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (abs_nonneg v) (-s))) hpower
    simpa only [intervalIntegral_abs_rpow_symm hs1 (by linarith : 0 ≤ 4 * H)] using hh
  rw [intervalIntegral.integral_const_mul] at hnorm
  have hb := hnorm.trans (mul_le_mul_of_nonneg_left hint hD)
  refine (abs_sub _ _).trans ((add_le_add hsum hb).trans_eq ?_)
  dsimp [D]
  ring

/-- The absolute kernel sum is `O(N)` in either window, uniformly in its size. -/
theorem gradQuad_kernel_sum_crude {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → i ∈ gradLabels N ℓ γ →
      |(N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
        deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N)| ≤ C * (N : ℝ) := by
  obtain ⟨Cg, hCg, hg⟩ := gradSplit_derivative_bounds s hs0 hs1
  obtain ⟨Cd, hCd, hd⟩ := gradQuad_sum_erase_abs_pow_le hs0
  refine ⟨Cg * Cd, by positivity, ?_⟩
  intro N ℓ γ i hN hi
  have hNR : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hterm : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      |(N : ℝ) ^ (-s) * deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N)| ≤
        Cg * (N : ℝ) * |(gradPathIncr N ℓ γ i j : ℝ)| ^ (-1 - s) := by
    intro j hj
    obtain ⟨hne, hjl⟩ := Finset.mem_erase.mp hj
    have hk0 := gradPathIncr_ne_zero hi hjl hne
    have hkR : (gradPathIncr N ℓ γ i j : ℝ) ≠ 0 := by exact_mod_cast hk0
    have hkN : |(gradPathIncr N ℓ γ i j : ℝ)| ≤ (N : ℝ) / 2 := by
      have h : (2 : ℝ) * |(gradPathIncr N ℓ γ i j : ℝ)| ≤ (N : ℝ) := by
        exact_mod_cast two_abs_gradPathIncr_le hi hjl
      linarith
    have hr0 : 0 < |(gradPathIncr N ℓ γ i j : ℝ) / (N : ℝ)| :=
      abs_pos.mpr (div_ne_zero hkR hNR.ne')
    have hr1 : |(gradPathIncr N ℓ γ i j : ℝ) / (N : ℝ)| ≤ 3 / 4 := by
      rw [abs_div, abs_of_pos hNR, div_le_iff₀ hNR]; linarith
    have hb := (hg _ hr0 hr1).2 1 (by norm_num)
    simp only [iteratedDeriv_one, Nat.cast_one] at hb
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hNR.le _)]
    calc _ ≤ (N : ℝ) ^ (-s) * (Cg * |(gradPathIncr N ℓ γ i j : ℝ) / N| ^ (-s - 1)) := by gcongr
         _ = _ := by
          rw [mul_left_comm, gradPartial_kernel_deriv_scale hNR, mul_assoc]
          rw [show -s - 1 = -1 - s by ring]
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (hd N ℓ γ i hN hi) (by positivity : 0 ≤ Cg * (N : ℝ))
  exact hh.trans_eq (by ring)

/-- Scalar assembly of a split into two odd terms and a remainder. -/
lemma gradQuad_abs_split_bound {V q U W R A B D : ℝ}
    (hV : V = 2 * q * (U - W) + 2 * R)
    (hU : |q * U| ≤ A) (hW : |q * W| ≤ B) (hR : |R| ≤ D) :
    |V| ≤ 2 * A + 2 * B + 2 * D := by
  rw [hV, mul_sub]
  simp only [mul_assoc (2 : ℝ)]
  have ht := abs_add_le (2 * (q * U) - 2 * (q * W)) (2 * R)
  have hs := abs_sub (2 * (q * U)) (2 * (q * W))
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht hs hU hW
  nlinarith [ht, hs]

/-- Crude partial reference-field bound when the microscopic window is bounded by `H`.
No large-scale geometry is assumed. -/
theorem gradV2_partial_crude_bound {s α γ ε H : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) (hγ : 0 ≤ γ)
    (hε : ε ≤ γ * (1 - s / 2)) (hH : 1 ≤ H) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ+) (ℓ C0 : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → GradPartial N ℓ γ →
      gradM N ℓ γ ≤ H → 0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε → i ∈ gradLabels N ℓ γ →
      |gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i| ≤
        C * C0 * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) := by
  obtain ⟨Cr, hCr, hr⟩ := gradQuad_remainder_crude hs0 hs1 hα0 hα1 hH
  obtain ⟨Cs, hCs, hs⟩ := gradQuad_kernel_sum_crude hs0 hs1
  obtain ⟨Cb, hCb, hb⟩ := gradPartial_kernel_boundary_bound hs0 hs1
  refine ⟨2 * Cb + 2 * Cs + 2 * Cr, by positivity, ?_⟩
  intro N ℓ C0 X ψ i hN hℓ hℓ1 hK hP hMH hC0 hψ hper h1 h2 hsupp hX hanchor hi
  have hNR : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hx := gradPartial_anchor_lift_bound hs0 hγ hε hK hP hX hanchor hi
  have hrem := hr N ℓ γ C0 (gradLift N X i) ψ i hN hℓ hℓ1 hK hγ hP hMH hx hC0 hψ hper h1 h2 hi
  have hsum := hs N ℓ γ i hN hi
  have hq : |deriv ψ (gradLift N X i / ℓ)| ≤ C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) :=
    (h1 _).trans (mul_le_mul_of_nonneg_left (gradWeightOne_le_K_pow hs1 (by linarith) hK) hC0)
  let U := (N : ℝ) ^ (1 - s) *
    (gradKernelH s (gradT N ℓ γ - gradLift N X i) - gradKernelH s (-gradT N ℓ γ - gradLift N X i))
  let W := (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
    deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N)
  have hboundU : |deriv ψ (gradLift N X i / ℓ) * U| ≤
      Cb * C0 * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) := by
    by_cases hactive : |(N : ℝ) * gradLift N X i| ≤ gradM N ℓ γ / 3
    · have hn : 1 ≤ ⌊gradM N ℓ γ⌋ := Int.le_floor.mpr (by simpa using hM)
      have hnR : (1 : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hn
      have hh := hb N ℓ γ (gradLift N X i) hP hn (by linarith)
      have hnPow := Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith : -s ≤ 0)
      have hU : |U| ≤ Cb * (N : ℝ) := hh.trans (mul_le_of_le_one_right (by positivity) hnPow)
      rw [abs_mul]
      calc _ ≤ (C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) * (Cb * (N : ℝ)) :=
          mul_le_mul hq hU (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · have hz := gradQuad_inactive hψ hℓ hP (by linarith) hsupp hx (lt_of_not_ge hactive)
      rw [hz.2, zero_mul, abs_zero]; positivity
  have hboundW : |deriv ψ (gradLift N X i / ℓ) * W| ≤
      Cs * C0 * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) := by
    rw [abs_mul]
    calc _ ≤ (C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) * (Cs * (N : ℝ)) :=
        mul_le_mul hq hsum (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsplit := gradV2_partial_split hs0 hs1 hα0 hα1 hγ hε hN hℓ hℓ1 hK hP hC0 hψ
    hper h1 h2 hsupp X hX hanchor hi
  dsimp [W] at hboundW
  simp only [gradPathIncr, hP, ↓reduceIte] at hboundW hrem
  have ht := gradQuad_abs_split_bound hsplit hboundU hboundW hrem
  exact ht.trans_eq (by ring)

end

end Riesz1
