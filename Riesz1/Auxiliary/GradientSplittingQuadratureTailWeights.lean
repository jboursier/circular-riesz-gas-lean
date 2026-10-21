/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadratureStrips
public import Riesz1.Auxiliary.GradientSplittingQuadraturePowers
public import Riesz1.Auxiliary.GradientSplittingQuadratureOdd

/-!
# Absorbing the partial-window odd tails

The quadrature part of Lemma 5.7. The two exponent cases can be applied
at the spatial radius `|Nx|` itself, avoiding label-to-position weight losses.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The odd-tail scale times the first envelope is bounded by the two target weights.
This is an internal scalar estimate on the active part of a partial window. -/
theorem gradQuad_odd_weight_le {s a γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha : 0 ≤ a) (hγ4 : 4 ≤ γ) (hγs : 2 / s ≤ γ)
    {N : ℕ+} {ℓ x : ℝ} (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ)
    (hP : GradPartial N ℓ γ) (hx : |(N : ℝ) * x| ≤ gradM N ℓ γ / 3) :
    (N : ℝ) * gradWeightOne s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) *
        (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s)
      ≤ (2 ^ s + 2 ^ (1 + s / 2) * 2 ^ s) *
        (ℓ⁻¹ * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
          (N : ℝ) * ((N : ℝ) * ℓ) ^ a /
            (1 + (N : ℝ) * circDist 1 x) ^ (1 + s / 2)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK (by linarith)
  have hn : 1 ≤ ⌊gradM N ℓ γ⌋ := Int.le_floor.mpr (by simpa using hM)
  have hn0 : (0 : ℝ) < (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < ⌊gradM N ℓ γ⌋)
  have hfloor : ((N : ℝ) * ℓ) ^ γ ≤ 2 * (⌊gradM N ℓ γ⌋ : ℝ) := by
    change gradM N ℓ γ ≤ _
    have hr : (1 : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hn
    linarith [Int.lt_floor_add_one (gradM N ℓ γ)]
  have hxhalf : |x| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hN] at hx
    nlinarith [hP]
  have hc : circDist 1 x = |x| := by
    have he := gradQuad_circDist_scaled one_pos hxhalf
    simpa using he
  have hcs := gradQuad_circDist_scaled hℓ hxhalf
  have hur : |(N : ℝ) * x| = (N : ℝ) * |x| := by rw [abs_mul, abs_of_pos hN]
  let A := ℓ⁻¹ * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
  let B := (N : ℝ) * ((N : ℝ) * ℓ) ^ a / (1 + (N : ℝ) * circDist 1 x) ^ (1 + s / 2)
  have hA : 0 ≤ A := mul_nonneg (inv_nonneg.mpr hℓ.le) (gradWeightTwo_nonneg_unconditional _ _ _ _ _)
  have hB : 0 ≤ B := by dsimp [B]; rw [hc]; positivity
  have hcoef : 0 ≤ (2 : ℝ) ^ s + 2 ^ (1 + s / 2) * 2 ^ s := by positivity
  by_cases hu : |(N : ℝ) * x| ≤ (N : ℝ) * ℓ
  · have hd : circDist ℓ⁻¹ (x / ℓ) ≤ 1 := by
      rw [hcs, div_le_one hℓ]; rw [hur] at hu; nlinarith
    have hw := gradWeightOne_le_mul_gradWeightTwo (s := s) (a := a) hK hd
      ((inv_le_one₀ hK0).mpr hK)
    rw [one_mul] at hw
    have hp := gradPartial_inner_tail_ratio hs0.le
      (by linarith [(gradPartial_gamma_exponents hs0 hs1 ha hγ4 hγs).1] : 1 ≤ γ * s)
      hK hn0 hfloor
    have hW := gradWeightTwo_nonneg_unconditional s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ)
    have hscaled : (N : ℝ) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) ≤ 2 ^ s * ℓ⁻¹ := by
      apply (mul_le_mul_iff_right₀ hℓ).mp
      convert hp using 1 <;> field_simp
    have hb : (N : ℝ) * gradWeightOne s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) *
        (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) ≤ 2 ^ s * A := by
      calc _ ≤ (N : ℝ) * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) *
          (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) := by gcongr
        _ ≤ _ := by dsimp [A]; nlinarith [mul_le_mul_of_nonneg_right hscaled hW]
    exact hb.trans (by
      change _ ≤ _ * (A + B)
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (1 + s / 2) * 2 ^ s) hA,
        mul_nonneg hcoef hB])
  · have huK : (N : ℝ) * ℓ ≤ |(N : ℝ) * x| := le_of_not_ge hu
    have hu0 : 0 < |(N : ℝ) * x| := hK0.trans_le huK
    have huM : |(N : ℝ) * x| ≤ ((N : ℝ) * ℓ) ^ γ := by change _ ≤ gradM N ℓ γ; linarith
    have hp := gradPartial_outer_tail_ratio hs0 hs1 ha hγ4 hγs hK hn0 hfloor huK huM
    have hd : 1 ≤ circDist ℓ⁻¹ (x / ℓ) := by
      rw [hcs, le_div_iff₀ hℓ]; rw [hur] at huK; nlinarith
    have hw : gradWeightOne s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) =
        (|(N : ℝ) * x| / ((N : ℝ) * ℓ)) ^ (s - 2) := by
      rw [gradWeightOne_of_one_le hd, hcs, hur]
      congr 1; field_simp
    have hu1 : 1 ≤ |(N : ℝ) * x| := hK.trans huK
    have hdpos : 0 < (1 + |(N : ℝ) * x|) ^ (1 + s / 2) := by positivity
    have hbound : (1 + |(N : ℝ) * x|) ^ (1 + s / 2) ≤
        2 ^ (1 + s / 2) * |(N : ℝ) * x| ^ (1 + s / 2) := by
      rw [← Real.mul_rpow (by norm_num) hu0.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have hratio : ((N : ℝ) * ℓ) ^ (-a) *
        (|(N : ℝ) * x| / ((N : ℝ) * ℓ)) ^ (s - 2) *
        (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) * (1 + |(N : ℝ) * x|) ^ (1 + s / 2)
        ≤ 2 ^ (1 + s / 2) * 2 ^ s := by
      calc _ ≤ ((N : ℝ) * ℓ) ^ (-a) *
          (|(N : ℝ) * x| / ((N : ℝ) * ℓ)) ^ (s - 2) *
          (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) *
          (2 ^ (1 + s / 2) * |(N : ℝ) * x| ^ (1 + s / 2)) := by gcongr
        _ = 2 ^ (1 + s / 2) * (((N : ℝ) * ℓ) ^ (2 - s - a) *
            (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) * |(N : ℝ) * x| ^ (-1 + 3 * s / 2)) := by
          have eK : ((N : ℝ) * ℓ) ^ (-a) * ((N : ℝ) * ℓ) ^ (-(s - 2)) =
              ((N : ℝ) * ℓ) ^ (2 - s - a) := by
            rw [← Real.rpow_add hK0]; congr 1; ring
          have eR : |(N : ℝ) * x| ^ (s - 2) * |(N : ℝ) * x| ^ (1 + s / 2) =
              |(N : ℝ) * x| ^ (-1 + 3 * s / 2) := by
            rw [← Real.rpow_add hu0]; congr 1; ring
          calc _ = 2 ^ (1 + s / 2) *
              ((((N : ℝ) * ℓ) ^ (-a) * ((N : ℝ) * ℓ) ^ (-(s - 2))) *
                (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) *
                (|(N : ℝ) * x| ^ (s - 2) * |(N : ℝ) * x| ^ (1 + s / 2))) := by
                  rw [Real.div_rpow hu0.le hK0.le]
                  simp only [Real.rpow_neg hK0.le]
                  ring
               _ = _ := by rw [eK, eR]
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
    have hb : (N : ℝ) * gradWeightOne s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) *
        (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) ≤ (2 ^ (1 + s / 2) * 2 ^ s) * B := by
      rw [hw]
      dsimp [B]
      rw [hc, ← hur, ← mul_div_assoc, le_div_iff₀ hdpos]
      have hpowne : ((N : ℝ) * ℓ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hK0 _).ne'
      calc _ = ((N : ℝ) * ((N : ℝ) * ℓ) ^ a) *
          (((N : ℝ) * ℓ) ^ (-a) * (|(N : ℝ) * x| / ((N : ℝ) * ℓ)) ^ (s - 2) *
            (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) * (1 + |(N : ℝ) * x|) ^ (1 + s / 2)) := by
              rw [Real.rpow_neg hK0.le]; field_simp
           _ ≤ ((N : ℝ) * ((N : ℝ) * ℓ) ^ a) * (2 ^ (1 + s / 2) * 2 ^ s) :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
           _ = _ := by ring
    exact hb.trans (by
      change _ ≤ _ * (A + B)
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ s) hB, mul_nonneg hcoef hA])

/-- The odd part of the partial reference field has the target bound at large scales.
The derivative coefficient is retained, including where it vanishes by support. -/
theorem gradPartial_odd_large_bound {s α γ ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (_hα1 : α < s / 2) (hγ4 : 4 ≤ γ) (hγs : 2 / s ≤ γ)
    (hε0 : 0 ≤ ε) (hε : ε < γ * (1 - s / 2)) :
    ∃ C K₀ : ℝ, 0 < C ∧ 1 ≤ K₀ ∧
    ∀ (N : ℕ+) (ℓ C0 : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ) (i : ℤ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → K₀ ≤ (N : ℝ) * ℓ → GradPartial N ℓ γ →
      0 ≤ C0 → ContDiff ℝ ∞ ψ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε → i ∈ gradLabels N ℓ γ →
      |deriv ψ (gradLift N X i / ℓ) *
        ((N : ℝ) ^ (1 - s) *
          (gradKernelH s (gradT N ℓ γ - gradLift N X i) -
            gradKernelH s (-gradT N ℓ γ - gradLift N X i)) -
          (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
            deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N))|
        ≤ C * C0 *
          (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
            (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
              (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  obtain ⟨Co, hCo, hodd⟩ := gradPartial_odd_contribution_bound hs0 hs1
  obtain ⟨K₀, hK₀, hsmall⟩ := gradQuad_small_relative_error hs0.le (by linarith) hε0 hε
  refine ⟨Co * (2 ^ s + 2 ^ (1 + s / 2) * 2 ^ s), K₀, by positivity, hK₀, ?_⟩
  intro N ℓ C0 X ψ i hN hℓ hℓ1 hK0 hP hC0 hψ h1 hsupp hX hanchor hi
  have hK := hK₀.trans hK0
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK (by linarith)
  have hx := gradPartial_anchor_lift_bound hs0 (by linarith) hε.le hK hP hX hanchor hi
  have he := gradPartial_anchor_error hs0 hP hX hanchor hi
  have hi' := (mem_gradLabels_partial hP i).mp hi
  have hir : |(i : ℝ)| ≤ gradM N ℓ γ := by
    have hb : |(i : ℝ)| ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by
      rw [← Int.cast_abs]; exact_mod_cast (abs_le.mpr ⟨hi'.1, hi'.2⟩)
    exact hb.trans (Int.floor_le _)
  have herr : 1 + |(N : ℝ) * gradLift N X i - (i : ℝ)| ≤ gradM N ℓ γ / 6 := by
    have hb := hsmall ((N : ℝ) * ℓ) hK0
    change 1 + ((N : ℝ) * ℓ) ^ ε * (1 + (gradM N ℓ γ) ^ (s / 2)) ≤ gradM N ℓ γ / 6 at hb
    have hm := Real.rpow_le_rpow (abs_nonneg (i : ℝ)) hir (by linarith : 0 ≤ s / 2)
    nlinarith [mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (by linarith : 0 ≤ (N : ℝ) * ℓ) ε)]
  have hM4 : 4 ≤ gradM N ℓ γ := by linarith [abs_nonneg ((N : ℝ) * gradLift N X i - (i : ℝ))]
  have hW := gradWeightTwo_nonneg_unconditional s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹
    (gradLift N X i / ℓ)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  by_cases hactive : |(N : ℝ) * gradLift N X i| ≤ gradM N ℓ γ / 3
  · have hgeom := gradQuad_active_geometry hM4 hactive herr
    have hn : 1 ≤ ⌊gradM N ℓ γ⌋ := Int.le_floor.mpr (by simpa using hM)
    have ho := hodd N ℓ γ (gradLift N X i) i hP hn hgeom.2 hgeom.1
    have hw := gradQuad_odd_weight_le hs0 hs1 (by linarith : 0 ≤ 1 - s + α)
      hγ4 hγs hℓ hK hP hactive
    have hW1 := gradWeightOne_nonneg_unconditional s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹
      (gradLift N X i / ℓ)
    rw [abs_mul]
    calc _ ≤ (C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)) *
        (Co * (N : ℝ) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s)) :=
          mul_le_mul (h1 _) ho (abs_nonneg _) (by positivity)
      _ = Co * C0 * ((N : ℝ) * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹
          (gradLift N X i / ℓ) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s)) := by ring
      _ ≤ Co * C0 * ((2 ^ s + 2 ^ (1 + s / 2) * 2 ^ s) * _) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring
  · have hz := gradQuad_inactive hψ hℓ hP (by linarith) hsupp hx (lt_of_not_ge hactive)
    rw [hz.2, zero_mul, abs_zero]
    have hc := circDist_nonneg 1 (gradLift N X i)
    positivity

end

end Riesz1
