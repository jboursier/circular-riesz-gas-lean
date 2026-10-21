/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingDisplacementEvent
public import Riesz1.Auxiliary.GradientSplittingWindowSupport
public import Riesz1.Auxiliary.GradientSplittingQuadraturePartialWeights

/-!
# Integrated mismatch-strip estimates

The quadrature part of Lemma 5.7. Active particles see both strips away
from zero and at larger weight distance. Inactive particles contribute zero there.
The event and anchor absorb the strip lengths into one factor `(Nℓ)^ε`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- A uniform threshold after which the floor and anchor errors are less than one sixth of the window.
It depends only on `s, γ, ε`. -/
lemma gradQuad_small_relative_error {s γ ε : ℝ} (hs : 0 ≤ s) (hγ : 0 ≤ γ)
    (hε0 : 0 ≤ ε) (hε : ε < γ * (1 - s / 2)) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      1 + K ^ ε * (1 + (K ^ γ) ^ (s / 2)) ≤ K ^ γ / 6 := by
  let p := ε + γ * (s / 2)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hd : 0 < γ - p := by dsimp [p]; nlinarith
  obtain ⟨L, hL⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop hd).eventually (eventually_ge_atTop (18 : ℝ)))
  refine ⟨max 1 L, le_max_left _ _, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := (le_max_left _ _).trans hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hpow := hL K ((le_max_right _ _).trans hK)
  have h1 : 1 ≤ K ^ p := Real.one_le_rpow hK1 hp
  have he : K ^ ε ≤ K ^ p := Real.rpow_le_rpow_of_exponent_le hK1
    (by dsimp [p]; nlinarith [mul_nonneg hγ hs])
  have hprod : K ^ ε * (K ^ γ) ^ (s / 2) = K ^ p := by
    rw [← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
  have hM : K ^ γ = K ^ (γ - p) * K ^ p := by
    rw [← Real.rpow_add hK0, sub_add_cancel]
  have h18 : 18 * K ^ p ≤ K ^ γ := by
    rw [hM]
    exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hK0.le p)
  nlinarith [hprod]


/-- Outside the central third of the support window, both coefficients vanish.
The strict margin allows the derivative to be treated using a neighbourhood. -/
lemma gradQuad_inactive {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {N : ℕ+} {ℓ γ x : ℝ} (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ)
    (hM : 0 < gradM N ℓ γ)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (hx : |(N : ℝ) * x| ≤ 3 * gradM N ℓ γ)
    (hfar : gradM N ℓ γ / 3 < |(N : ℝ) * x|) :
    ψ (x / ℓ) = 0 ∧ deriv ψ (x / ℓ) = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have ht : gradT N ℓ γ = gradM N ℓ γ / N := by simp [gradT, hP]
  have htr : 0 < gradT N ℓ γ ∧ gradT N ℓ γ < 1 / 8 := by
    rw [ht]; constructor
    · positivity
    · apply (div_lt_iff₀ hN).mpr; linarith [hP]
  rw [abs_mul, abs_of_pos hN] at hx hfar
  have hxl : gradT N ℓ γ / 4 < |x| := by rw [ht, div_div]; apply (div_lt_iff₀ (by positivity : 0 < (N : ℝ) * 4)).mpr; nlinarith
  have hxu : |x| < 1 / 2 := by nlinarith [hP]
  have hz : ∀ᶠ y in 𝓝 x, ψ (y / ℓ) = 0 := by
    have he1 : ∀ᶠ y in 𝓝 x, gradT N ℓ γ / 4 < |y| :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds hxl
    have he2 : ∀ᶠ y in 𝓝 x, |y| < 1 / 2 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds hxu
    have he := he1.and he2
    filter_upwards [he] with y hy
    exact hsupp y (gradPartial_far_from_int (by linarith : gradT N ℓ γ ≤ 1 / 2) hy.1.le hy.2.le)
  exact ⟨hz.self_of_nhds, deriv_psi_zero_of_eventually hℓ.ne' hz
    (hψ.differentiable (by simp) _)⟩

/-- An active profile forces the particle and its label into the middle of the window. -/
lemma gradQuad_active_geometry {M u : ℝ} {i : ℤ} (hM : 4 ≤ M)
    (hx : |u| ≤ M / 3) (he : 1 + |u - (i : ℝ)| ≤ M / 6) :
    |u| ≤ M / 2 ∧ 2 * |i| ≤ ⌊M⌋ := by
  have ht := abs_add_le ((i : ℝ) - u) u
  rw [sub_add_cancel, abs_sub_comm] at ht
  have hi : 2 * |(i : ℝ)| ≤ (⌊M⌋ : ℝ) := by
    linarith [Int.lt_floor_add_one M]
  exact ⟨by linarith, by exact_mod_cast hi⟩

/-- Within half a period, scaled circular distance is the scaled absolute value. -/
lemma gradQuad_circDist_scaled {ℓ y : ℝ} (hℓ : 0 < ℓ) (hy : |y| ≤ 1 / 2) :
    circDist ℓ⁻¹ (y / ℓ) = |y| / ℓ := by
  have he : circDist 1 y = |y| := by
    rcases le_or_gt 0 y with h | h
    · rw [circDist_of_mem_Icc one_pos h (by rwa [abs_of_nonneg h] at hy), abs_of_nonneg h]
    · have hb := circDist_neg_of_mem_Icc one_pos (by linarith : 0 ≤ -y)
        (by rwa [abs_of_neg h] at hy)
      simpa only [neg_neg, abs_of_neg h] using hb
  simpa only [one_div, he] using circDist_scale hℓ 1 y

/-- Active particles see the strips away from zero and at larger weight distance. -/
lemma gradQuad_active_strip_geometry {N : ℕ+} {ℓ γ x v : ℝ} {i : ℤ}
    (hP : GradPartial N ℓ γ) (hM : 0 ≤ gradM N ℓ γ)
    (hx : |(N : ℝ) * x| ≤ gradM N ℓ γ / 3)
    (he : 1 + |(N : ℝ) * x - (i : ℝ)| ≤ gradM N ℓ γ / 6)
    (hv : v ∈ uIcc (-gradM N ℓ γ - (N : ℝ) * x)
        (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2) ∨
      v ∈ uIcc (gradM N ℓ γ - (N : ℝ) * x)
        ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2)) :
    gradM N ℓ γ / 2 ≤ |v| ∧ |v| ≤ 3 * (N : ℝ) / 4 ∧
      |x| ≤ |x + v / (N : ℝ)| ∧ |x + v / (N : ℝ)| ≤ 1 / 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hl := gradPartial_strip_location hM i hv
  have ht0 := abs_sub ((N : ℝ) * x + v) ((N : ℝ) * x)
  rw [add_sub_cancel_left] at ht0
  have ht1 := abs_add_le ((N : ℝ) * x) v
  have hy : x + v / (N : ℝ) = ((N : ℝ) * x + v) / N := by field_simp
  refine ⟨by linarith, by linarith [hP], ?_, ?_⟩
  · rw [hy, abs_div, abs_of_pos hN, le_div_iff₀ hN]
    have hb : (N : ℝ) * |x| = |(N : ℝ) * x| := by rw [abs_mul, abs_of_pos hN]
    nlinarith [hb]
  · rw [hy, abs_div, abs_of_pos hN, div_le_iff₀ hN]
    linarith [hP]

/-- Quantitative bound for either mismatch strip. The small relative error is geometric,
not a bound on the quadrature conclusion. -/
theorem gradQuad_strip_integral_bound {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ C0 x : ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      |(N : ℝ) * x| ≤ 3 * gradM N ℓ γ →
      1 + |(N : ℝ) * x - (i : ℝ)| ≤ gradM N ℓ γ / 6 →
      (|∫ v in (-gradM N ℓ γ - (N : ℝ) * x)..
          (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v| +
        |∫ v in (gradM N ℓ γ - (N : ℝ) * x)..
          ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2), gradCellR s (N : ℕ) ℓ ψ x v|)
        ≤ C * C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) *
          (gradM N ℓ γ) ^ (-s) * (1 + |(N : ℝ) * x - (i : ℝ)|) := by
  obtain ⟨Cc, hCc, hcells⟩ := gradient_splitting_cells hs0 hs1 hα0 hα1
  refine ⟨4 * Cc * 2 ^ s, by positivity, ?_⟩
  intro N ℓ γ C0 x ψ i hN hℓ hℓ1 hK hγ hP hC0 hψ hper h1 h2 hsupp hx he
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hM0 : 0 < gradM N ℓ γ := by linarith
  have hW : 0 ≤ gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) :=
    gradWeightTwo_nonneg_unconditional _ _ _ _ _
  let D := 2 * Cc * 2 ^ s * C0 * ℓ⁻¹ *
    gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) * (gradM N ℓ γ) ^ (-s)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint : ∀ v : ℝ,
      (v ∈ uIcc (-gradM N ℓ γ - (N : ℝ) * x)
          (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2) ∨
        v ∈ uIcc (gradM N ℓ γ - (N : ℝ) * x)
          ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2)) →
      |gradCellR s (N : ℕ) ℓ ψ x v| ≤ D := by
    intro v hv
    have hys := gradPartial_strip_support hP hM0.le hsupp i (by linarith) hv
    by_cases hactive : |(N : ℝ) * x| ≤ gradM N ℓ γ / 3
    · obtain ⟨hv0, hvN, hxy, hy⟩ := gradQuad_active_strip_geometry hP hM0.le hactive he hv
      have hxhalf : |x| ≤ 1 / 2 := hxy.trans hy
      have hw := gradWeightTwo_le_of_circDist_le hs1 (by linarith : 0 ≤ 1 - s + α) hK
        (show circDist ℓ⁻¹ (x / ℓ) ≤ circDist ℓ⁻¹ ((x + v / N) / ℓ) by
          rw [gradQuad_circDist_scaled hℓ hxhalf, gradQuad_circDist_scaled hℓ hy]
          exact div_le_div_of_nonneg_right hxy hℓ.le)
      have hWy : 0 ≤ gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹
          ((x + v / N) / ℓ) := gradWeightTwo_nonneg_unconditional _ _ _ _ _
      have hp := (hcells (N : ℕ) ℓ C0 x ψ hN hℓ hℓ1 hK hC0 hψ hper h1 h2).2.1
        v (by linarith) hvN
      have hvpow : |v| ^ (-s) ≤ 2 ^ s * (gradM N ℓ γ) ^ (-s) := by
        calc _ ≤ (gradM N ℓ γ / 2) ^ (-s) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hv0 (by linarith)
          _ = _ := by
            rw [Real.div_rpow hM0.le (by norm_num),
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
      calc _ ≤ Cc * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) *
              (2 ^ s * (gradM N ℓ γ) ^ (-s)) := hp.trans (mul_le_mul_of_nonneg_left hvpow (by positivity))
        _ ≤ Cc * C0 * ℓ⁻¹ *
          (gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
            gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)) *
              (2 ^ s * (gradM N ℓ γ) ^ (-s)) := by gcongr
        _ = D := by dsimp [D]; ring
    · have hz := gradQuad_inactive hψ hℓ hP hM0 hsupp hx (lt_of_not_ge hactive)
      rw [(gradPartial_cell_vanish hψ hℓ s (N : ℕ) x v hz.1 hz.2 hys).2]
      simpa only [abs_zero] using hD
  have hl := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := gradCellR s (N : ℕ) ℓ ψ x)
    (a := -gradM N ℓ γ - (N : ℝ) * x)
    (b := -(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2)
    (C := D) (by
      intro v hv
      simpa only [Real.norm_eq_abs] using hpoint v (Or.inl (uIoc_subset_uIcc hv)))
  have hr := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := gradCellR s (N : ℕ) ℓ ψ x)
    (a := gradM N ℓ γ - (N : ℝ) * x)
    (b := (⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2)
    (C := D) (by
      intro v hv
      simpa only [Real.norm_eq_abs] using hpoint v (Or.inr (uIoc_subset_uIcc hv)))
  simp only [Real.norm_eq_abs] at hl hr
  have hlen := gradPartial_strip_length (M := gradM N ℓ γ) (u := (N : ℝ) * x) i
  rw [abs_sub_comm] at hl hr
  have hb := add_le_add (hl.trans (mul_le_mul_of_nonneg_left hlen.1 hD))
    (hr.trans (mul_le_mul_of_nonneg_left hlen.2 hD))
  exact hb.trans_eq (by dsimp [D]; ring)

/-- The strip length times its kernel power costs only `K^ε`. -/
lemma gradQuad_strip_length_power {s M K ε r e : ℝ} (hs : 0 ≤ s) (hM : 1 ≤ M)
    (hK : 1 ≤ K) (hε : 0 ≤ ε) (hr0 : 0 ≤ r) (hr : r ≤ M)
    (he : e ≤ K ^ ε * (1 + r ^ (s / 2))) :
    M ^ (-s) * (1 + e) ≤ 3 * K ^ ε := by
  have hM0 : 0 < M := by linarith
  have hm : M ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
  have hp : M ^ (-s / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
  have hpow : M ^ (-s) * r ^ (s / 2) ≤ 1 := by
    calc _ ≤ M ^ (-s) * M ^ (s / 2) := by gcongr
      _ = M ^ (-s / 2) := by rw [← Real.rpow_add hM0]; congr 1; ring
      _ ≤ 1 := hp
  have hk := Real.one_le_rpow hK hε
  have he' := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hM0.le (-s))
  nlinarith [mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (by linarith : 0 ≤ K) ε),
    mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by linarith : 0 ≤ K) ε)]

/-- Both mismatch strip integrals have the first target weight, on the event and anchor,
for all sufficiently large scales. -/
theorem gradPartial_strips_bound {s α γ ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) (hγ : 0 ≤ γ)
    (hε0 : 0 ≤ ε) (hε : ε < γ * (1 - s / 2)) :
    ∃ C K₀ : ℝ, 0 < C ∧ 1 ≤ K₀ ∧
    ∀ (N : ℕ+) (ℓ C0 : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → K₀ ≤ (N : ℝ) * ℓ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε → i ∈ gradLabels N ℓ γ →
      (|∫ v in (-gradM N ℓ γ - (N : ℝ) * gradLift N X i)..
          (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2),
            gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) v| +
        |∫ v in (gradM N ℓ γ - (N : ℝ) * gradLift N X i)..
          ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2),
            gradCellR s (N : ℕ) ℓ ψ (gradLift N X i) v|)
        ≤ C * C0 * ((N : ℝ) * ℓ) ^ ε * ℓ⁻¹ *
          gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) := by
  obtain ⟨C, hC, hstrip⟩ := gradQuad_strip_integral_bound hs0 hs1 hα0 hα1
  obtain ⟨K₀, hK₀, hsmall⟩ := gradQuad_small_relative_error hs0.le hγ hε0 hε
  refine ⟨3 * C, K₀, by positivity, hK₀, ?_⟩
  intro N ℓ C0 X ψ i hN hℓ hℓ1 hK0 hP hC0 hψ hper h1 h2 hsupp hX hanchor hi
  have hK := hK₀.trans hK0
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hi' := (mem_gradLabels_partial hP i).mp hi
  have hir : |(i : ℝ)| ≤ gradM N ℓ γ := by
    have hb : |(i : ℝ)| ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by
      rw [← Int.cast_abs]; exact_mod_cast (abs_le.mpr ⟨hi'.1, hi'.2⟩)
    exact hb.trans (Int.floor_le _)
  have he := gradPartial_anchor_error hs0 hP hX hanchor hi
  have hx := gradPartial_anchor_lift_bound hs0 hγ hε.le hK hP hX hanchor hi
  have herr : 1 + |(N : ℝ) * gradLift N X i - (i : ℝ)| ≤ gradM N ℓ γ / 6 := by
    have hb := hsmall ((N : ℝ) * ℓ) hK0
    change 1 + ((N : ℝ) * ℓ) ^ ε * (1 + (gradM N ℓ γ) ^ (s / 2)) ≤ gradM N ℓ γ / 6 at hb
    have hm := Real.rpow_le_rpow (abs_nonneg (i : ℝ)) hir (by linarith : 0 ≤ s / 2)
    nlinarith [mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (by linarith : 0 ≤ (N : ℝ) * ℓ) ε)]
  have hb := hstrip N ℓ γ C0 (gradLift N X i) ψ i hN hℓ hℓ1 hK hγ hP hC0 hψ hper
    h1 h2 hsupp hx herr
  have hp := gradQuad_strip_length_power hs0.le hM hK hε0 (abs_nonneg (i : ℝ)) hir he
  have hcoef : 0 ≤ C * C0 * ℓ⁻¹ *
      gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) := by
    have := gradWeightTwo_nonneg_unconditional s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹
      (gradLift N X i / ℓ)
    positivity
  calc _ ≤ _ := hb
       _ ≤ C * C0 * ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹
          (gradLift N X i / ℓ) * (3 * ((N : ℝ) * ℓ) ^ ε) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hcoef
       _ = _ := by ring

end

end Riesz1
