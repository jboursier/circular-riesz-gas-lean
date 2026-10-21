/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffPairBound
public import Riesz1.Auxiliary.LoopCutoffEnvelope
public import Riesz1.Auxiliary.LoopCutoffEvent
public import Riesz1.ToMathlib.AbsRpowRadius

/-!
# The bound `|F^*_γ| ≤ C C_0 K^{B_1}` of the anchored cutoff

The cutoff part of Lemma 5.8, the clause `|F^*_γ| ≤ C C_0 K^{B_1}`. The function
`F^*_γ = η^* H^*` is bounded by `|H^*|` on the support of the cutoff, and `|H^*|` is the localized
loop `gradLoop` of the transport `ψ_γ`. The loop is bounded term by term:

* the pair terms by `N^{-s} |h| ≤ C (2K^ε)^{s+1}` (`loopPair_term_bound`), and the divided
  differences by the uniform bound `|Z| ≤ C C_0 K^a` (`gradZ_abs_le_const`, with the envelope of
  `ψ_γ` and `w_1 ≤ K^a`).
* the background integrals by `∫ |y - x|^{-s} dy` over an interval of radius `R`, where `R` is
  `5M/N` in a partial window (using the anchor `x_0 = 0`) and `1/2` in a full window.

Everything is deterministic: the rigidity theorem is not used.
-/

@[expose] public section

open Finset MeasureTheory Set
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The background integral of the localized loop is bounded by the radius `R` of its interval:
`|∫_B Z(x,y) h(y - x) dy| ≤ C_Z C_h · 2 R^{1-s}/(1-s)` when `B` is contained in `[x - R, x + R]`
and `|y - x| ≤ 3/4` on `B`. -/
lemma loopBackground_bound {s ℓ γ x Zb Cb R : ℝ} {N : ℕ+} {ψ : ℝ → ℝ} (hs1 : s < 1) (hR : 0 ≤ R)
    (hZb : 0 ≤ Zb) (hCb : 0 ≤ Cb) (hZ : ∀ t, |gradZ ψ ℓ x t| ≤ Zb)
    (hh : ∀ r : ℝ, |r| ≤ 3 / 4 → |gradKernelH s r| ≤ Cb * |r| ^ (-s))
    (hab : gradBLo N ℓ γ x ≤ gradBHi N ℓ γ x)
    (hlo : x - R ≤ gradBLo N ℓ γ x) (hhi : gradBHi N ℓ γ x ≤ x + R)
    (hsmall : ∀ y : ℝ, gradBLo N ℓ γ x ≤ y → y ≤ gradBHi N ℓ γ x → |y - x| ≤ 3 / 4) :
    |gradBackground s ψ N ℓ γ x| ≤ Zb * Cb * (2 * R ^ (1 - s) / (1 - s)) := by
  unfold gradBackground
  have hint := intervalIntegrable_abs_sub_rpow_radius hs1 hR hab hlo hhi
  have hbound : IntervalIntegrable (fun y : ℝ => (Zb * Cb) * |y - x| ^ (-s)) volume
      (gradBLo N ℓ γ x) (gradBHi N ℓ γ x) := hint.const_mul _
  have hpt : ∀ t : ℝ, t ∈ Set.Ioc (gradBLo N ℓ γ x) (gradBHi N ℓ γ x) →
      ‖gradZ ψ ℓ x t * gradKernelH s (t - x)‖ ≤ (Zb * Cb) * |t - x| ^ (-s) := by
    intro t ht
    have hs := hsmall t ht.1.le ht.2
    rw [Real.norm_eq_abs, abs_mul]
    calc |gradZ ψ ℓ x t| * |gradKernelH s (t - x)| ≤ Zb * (Cb * |t - x| ^ (-s)) :=
          mul_le_mul (hZ t) (hh (t - x) hs) (abs_nonneg _) hZb
      _ = (Zb * Cb) * |t - x| ^ (-s) := by ring
  calc |∫ t in gradBLo N ℓ γ x..gradBHi N ℓ γ x, gradZ ψ ℓ x t * gradKernelH s (t - x)|
      = ‖∫ t in gradBLo N ℓ γ x..gradBHi N ℓ γ x, gradZ ψ ℓ x t * gradKernelH s (t - x)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in gradBLo N ℓ γ x..gradBHi N ℓ γ x, (Zb * Cb) * |t - x| ^ (-s) :=
        intervalIntegral.norm_integral_le_of_norm_le hab
          (Filter.Eventually.of_forall fun t ht => hpt t ht) hbound
    _ = (Zb * Cb) * ∫ t in gradBLo N ℓ γ x..gradBHi N ℓ γ x, |t - x| ^ (-s) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ (Zb * Cb) * (2 * R ^ (1 - s) / (1 - s)) :=
        mul_le_mul_of_nonneg_left (integral_abs_sub_rpow_le_radius hs1 hR hab hlo hhi)
          (mul_nonneg hZb hCb)
    _ = Zb * Cb * (2 * R ^ (1 - s) / (1 - s)) := by ring

/-- In a partial window, the preceding-particle anchor `x_0 = 0` keeps every label of the window
within `4 M/N` of the origin, where `M = K^γ`, under the good event. -/
lemma loopAnchor_abs_le {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hγ : 1 ≤ γ) (hεs : ε ≤ 1 - s / 2) (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ)
    (hev : gradEvent s (2 * γ) ε N ℓ X) (hX : X ⟨0, N.pos⟩ = 0) (i : ℤ)
    (hP : GradPartial N ℓ γ) (hi : i ∈ gradLabels N ℓ γ) :
    |gradLift N X i| ≤ 4 * (gradM N ℓ γ / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hM8 : gradM N ℓ γ < (N : ℝ) / 8 := hP
  have hM0 : 0 ≤ gradM N ℓ γ := Real.rpow_nonneg (by linarith) _
  have hfl := (mem_gradLabels_partial hP i).1 hi
  have hz : (0 : ℤ) ∈ gradLabels N ℓ γ := by
    rw [mem_gradLabels_partial hP]
    have : (0 : ℤ) ≤ ⌊gradM N ℓ γ⌋ := Int.floor_nonneg.mpr hM0
    constructor <;> omega
  have hiabs : |i| ≤ ⌊gradM N ℓ γ⌋ := abs_le.mpr ⟨by omega, by omega⟩
  have hfl_le : (⌊gradM N ℓ γ⌋ : ℝ) ≤ gradM N ℓ γ := Int.floor_le _
  have hiR : |(i : ℝ)| ≤ 2 * gradM N ℓ γ := by
    have h : ((|i| : ℤ) : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hiabs
    rw [Int.cast_abs] at h
    linarith
  have hk2 : 2 * |i| ≤ (N : ℤ) := by
    have h : (8 : ℝ) * ⌊gradM N ℓ γ⌋ < N := by linarith
    have h' : 8 * ⌊gradM N ℓ γ⌋ < (N : ℤ) := by exact_mod_cast h
    linarith
  have hev2 := gradEvent_pair_bound hev hℓ 0 i hk2
    (loop_pair_window_two (by linarith) (by linarith) (Or.inr ⟨hz, by rw [zero_add]; exact hi⟩))
  rw [zero_add, gradLift_zero_of_anchor hX, sub_zero] at hev2
  have hKε : ((N : ℝ) * ℓ) ^ ε * |(i : ℝ)| ^ (s / 2) ≤ 2 * gradM N ℓ γ :=
    loopRpow_mul_le hK hs0.le (by linarith) hγ hεs (abs_nonneg _) hiR
  have htri := abs_add_le ((N : ℝ) * gradLift N X i - (i : ℝ)) (i : ℝ)
  rw [sub_add_cancel] at htri
  have h1 : |(N : ℝ) * gradLift N X i| ≤ 4 * gradM N ℓ γ := by linarith
  rw [abs_mul, abs_of_pos hNpos] at h1
  rw [← mul_div_assoc, le_div_iff₀ hNpos]
  linarith

/-- Uniform background radius. In a partial window `R = 5M/N` covers the interval `[-M/N, M/N]`
together with the anchored labels. In a full window `R = 1/2` covers the full circle. In both cases
`N^{1-s} R^{1-s} ≤ 8M`, and every background integral of the window is bounded by the same
constant. -/
lemma loopBackground_uniform {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {ψ : ℝ → ℝ}
    {Cb Zb : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hCb : 0 ≤ Cb) (hZb : 0 ≤ Zb)
    (hb1 : ∀ r : ℝ, |r| ≤ 3 / 4 → |gradKernelH s r| ≤ Cb * |r| ^ (-s))
    (hZ : ∀ x y : ℝ, |gradZ ψ ℓ x y| ≤ Zb)
    (hγ : 1 ≤ γ) (hεs : ε ≤ 1 - s / 2) (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ)
    (hev : gradEvent s (2 * γ) ε N ℓ X) (hX : X ⟨0, N.pos⟩ = 0) :
    ∃ R : ℝ, 0 ≤ R ∧ (N : ℝ) ^ (1 - s) * R ^ (1 - s) ≤ 8 * gradM N ℓ γ ∧
      ∀ i ∈ gradLabels N ℓ γ,
        |gradBackground s ψ N ℓ γ (gradLift N X i)| ≤
          Zb * Cb * (2 * R ^ (1 - s) / (1 - s)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr N.pos
  have hM0 : 0 ≤ gradM N ℓ γ := Real.rpow_nonneg (by linarith) _
  have hM1 : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK (by linarith)
  have hs1' : 0 ≤ 1 - s := by linarith
  by_cases hP : GradPartial N ℓ γ
  · have hM8 : gradM N ℓ γ < (N : ℝ) / 8 := hP
    have ht0 : 0 ≤ gradM N ℓ γ / N := div_nonneg hM0 hNpos.le
    have ht8 : gradM N ℓ γ / N < 1 / 8 := by
      rw [div_lt_iff₀ hNpos]
      linarith
    refine ⟨5 * (gradM N ℓ γ / N), by linarith, ?_, ?_⟩
    · have hprod : (N : ℝ) * (5 * (gradM N ℓ γ / N)) = 5 * gradM N ℓ γ := by
        field_simp
      have hmul : (N : ℝ) ^ (1 - s) * (5 * (gradM N ℓ γ / N)) ^ (1 - s) =
          (5 * gradM N ℓ γ) ^ (1 - s) := by
        rw [← Real.mul_rpow hNpos.le (by linarith), hprod]
      rw [hmul]
      calc (5 * gradM N ℓ γ) ^ (1 - s) ≤ (5 * gradM N ℓ γ) ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le
            · linarith
            · linarith
        _ = 5 * gradM N ℓ γ := Real.rpow_one _
        _ ≤ 8 * gradM N ℓ γ := by linarith
    · intro i hi
      have hPi : GradPartial N ℓ γ := hP
      have hx := loopAnchor_abs_le hs0 hs1 hγ hεs hℓ hK hev hX i hP hi
      have hab : gradBLo N ℓ γ (gradLift N X i) ≤ gradBHi N ℓ γ (gradLift N X i) := by
        simp only [gradBLo, gradBHi, gradT, hP, ↓reduceIte]
        linarith
      have hlo : gradLift N X i - 5 * (gradM N ℓ γ / N) ≤ gradBLo N ℓ γ (gradLift N X i) := by
        simp only [gradBLo, gradT, hP, ↓reduceIte]
        linarith [abs_le.mp hx]
      have hhi : gradBHi N ℓ γ (gradLift N X i) ≤ gradLift N X i + 5 * (gradM N ℓ γ / N) := by
        simp only [gradBHi, gradT, hP, ↓reduceIte]
        linarith [abs_le.mp hx]
      have hsmall : ∀ y : ℝ, gradBLo N ℓ γ (gradLift N X i) ≤ y →
          y ≤ gradBHi N ℓ γ (gradLift N X i) → |y - gradLift N X i| ≤ 3 / 4 := by
        intro y hy1 hy2
        simp only [gradBLo, gradBHi, gradT, hP, ↓reduceIte] at hy1 hy2
        rw [abs_le]
        constructor <;> linarith [abs_le.mp hx]
      exact loopBackground_bound (N := N) (ψ := ψ) hs1 (by linarith) hZb hCb (hZ _)
        (fun r hr => hb1 r hr) hab hlo hhi hsmall
  · have hN8 : (N : ℝ) ≤ 8 * gradM N ℓ γ := by
      have := not_lt.mp hP
      linarith
    refine ⟨1 / 2, by norm_num, ?_, ?_⟩
    · have hhalf : (1 / 2 : ℝ) ^ (1 - s) ≤ 1 :=
        Real.rpow_le_one (by norm_num) (by norm_num) hs1'
      have hNs : (N : ℝ) ^ (1 - s) ≤ (N : ℝ) := by
        calc (N : ℝ) ^ (1 - s) ≤ (N : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
          _ = (N : ℝ) := Real.rpow_one _
      have hpos : 0 ≤ (N : ℝ) ^ (1 - s) := Real.rpow_nonneg hNpos.le _
      calc (N : ℝ) ^ (1 - s) * (1 / 2 : ℝ) ^ (1 - s) ≤ (N : ℝ) ^ (1 - s) * 1 :=
            mul_le_mul_of_nonneg_left hhalf hpos
        _ = (N : ℝ) ^ (1 - s) := mul_one _
        _ ≤ (N : ℝ) := hNs
        _ ≤ 8 * gradM N ℓ γ := hN8
    · intro i _
      have hab : gradBLo N ℓ γ (gradLift N X i) ≤ gradBHi N ℓ γ (gradLift N X i) := by
        simp only [gradBLo, gradBHi, hP, ↓reduceIte]
        linarith
      have hlo : gradLift N X i - 1 / 2 ≤ gradBLo N ℓ γ (gradLift N X i) := by
        simp only [gradBLo, hP, ↓reduceIte]
        linarith
      have hhi : gradBHi N ℓ γ (gradLift N X i) ≤ gradLift N X i + 1 / 2 := by
        simp only [gradBHi, hP, ↓reduceIte]
        linarith
      have hsmall : ∀ y : ℝ, gradBLo N ℓ γ (gradLift N X i) ≤ y →
          y ≤ gradBHi N ℓ γ (gradLift N X i) → |y - gradLift N X i| ≤ 3 / 4 := by
        intro y hy1 hy2
        simp only [gradBLo, gradBHi, hP, ↓reduceIte] at hy1 hy2
        rw [abs_le]
        constructor <;> linarith
      exact loopBackground_bound (N := N) (ψ := ψ) hs1 (by norm_num) hZb hCb (hZ _)
        (fun r hr => hb1 r hr) hab hlo hhi hsmall

/-- Each pair term of the localized loop, multiplied by `N^{-s}`, is bounded by `C_Z C_h (2 K^ε)^{s+1}`
(with `C_Z` the uniform divided-difference bound). -/
lemma loopPair_term_bound {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {ψ : ℝ → ℝ} {Cb Zb : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hCb : 0 ≤ Cb) (hZb : 0 ≤ Zb)
    (hb1 : ∀ r : ℝ, |r| ≤ 3 / 4 → |gradKernelH s r| ≤ Cb * |r| ^ (-s))
    (hb2 : ∀ r : ℝ, 3 / 4 < r → r < 1 → |gradKernelH s r| ≤ Cb * (1 - r) ^ (-s - 1))
    (hZ : ∀ x y : ℝ, |gradZ ψ ℓ x y| ≤ Zb)
    (hγ : 1 ≤ γ) (hε0 : 0 < ε) (hεs : ε ≤ 1 - s / 2) (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ)
    (hev : gradEvent s (2 * γ) ε N ℓ X) {i j : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) :
    (N : ℝ) ^ (-s) * |gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
        gradKernelH s (gradSep N ℓ γ X i j)| ≤
      Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1))) := by
  obtain ⟨hk, hw⟩ := loopPathIncr_spec hi hj
  have hpair : (N : ℝ) ^ (-s) * |gradKernelH s (gradSep N ℓ γ X i j)| ≤
      Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1)) :=
    loopPair_kernel_bound hs0 hs1 hCb hb1 hb2 hγ hε0 hεs hℓ hK hev i
      (gradPathIncr N ℓ γ i j) hk hw
  have hZ' := hZ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
  have hN0 : 0 ≤ (N : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [abs_mul]
  calc (N : ℝ) ^ (-s) * (|gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)| *
        |gradKernelH s (gradSep N ℓ γ X i j)|)
      = |gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)| *
          ((N : ℝ) ^ (-s) * |gradKernelH s (gradSep N ℓ γ X i j)|) := by ring
    _ ≤ Zb * ((N : ℝ) ^ (-s) * |gradKernelH s (gradSep N ℓ γ X i j)|) :=
        mul_le_mul_of_nonneg_right hZ' (mul_nonneg hN0 (abs_nonneg _))
    _ ≤ Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1))) :=
        mul_le_mul_of_nonneg_left hpair hZb

/-- A double sum over a finite set of labels, with the diagonal removed in the inner sum, bounded
by a weight times the number of pairs. -/
lemma loopSum_abs_le {L : Finset ℤ} {f : ℤ → ℤ → ℝ} {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hf : ∀ i ∈ L, ∀ j ∈ L.erase i, w * |f i j| ≤ c) :
    w * |∑ i ∈ L, ∑ j ∈ L.erase i, f i j| ≤ (L.card : ℝ) * ((L.card : ℝ) * c) := by
  have inner : ∀ i ∈ L, w * |∑ j ∈ L.erase i, f i j| ≤ (L.card : ℝ) * c := by
    intro i hi
    calc w * |∑ j ∈ L.erase i, f i j| ≤ w * ∑ j ∈ L.erase i, |f i j| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw
      _ = ∑ j ∈ L.erase i, w * |f i j| := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ L.erase i, c := Finset.sum_le_sum (fun j hj => hf i hi j hj)
      _ = ((L.erase i).card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (L.card : ℝ) * c :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hc
  calc w * |∑ i ∈ L, ∑ j ∈ L.erase i, f i j| ≤ w * ∑ i ∈ L, |∑ j ∈ L.erase i, f i j| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw
    _ = ∑ i ∈ L, w * |∑ j ∈ L.erase i, f i j| := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ L, (L.card : ℝ) * c := Finset.sum_le_sum (fun i hi => inner i hi)
    _ = (L.card : ℝ) * ((L.card : ℝ) * c) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The localized loop `H_γ[ψ_γ]` on the good event, uniformly in `ψ`: its size is at most
`C K^{...}`. The pair part is at most `(8M)^2` times the pair bound, and the background part is at
most `2 N^{1-s} (8M)` times the background bound, with `M = K^γ`. -/
lemma loopGradLoop_bound {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {ψ : ℝ → ℝ} {Cb Zb : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hCb : 0 ≤ Cb) (hZb : 0 ≤ Zb)
    (hb1 : ∀ r : ℝ, |r| ≤ 3 / 4 → |gradKernelH s r| ≤ Cb * |r| ^ (-s))
    (hb2 : ∀ r : ℝ, 3 / 4 < r → r < 1 → |gradKernelH s r| ≤ Cb * (1 - r) ^ (-s - 1))
    (hZ : ∀ x y : ℝ, |gradZ ψ ℓ x y| ≤ Zb)
    (hγ : 1 ≤ γ) (hε0 : 0 < ε) (hεs : ε ≤ 1 - s / 2) (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ)
    (hev : gradEvent s (2 * γ) ε N ℓ X) (hX : X ⟨0, N.pos⟩ = 0) :
    |gradLoop s ψ N ℓ γ X| ≤
      Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Zb * gradM N ℓ γ ^ 2 *
        (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) := by
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hM1 : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK (by linarith)
  have hq1 : 1 ≤ ((N : ℝ) * ℓ) ^ ε := Real.one_le_rpow hK hε0.le
  have hq0 : 0 ≤ ((N : ℝ) * ℓ) ^ ε := Real.rpow_nonneg hK0.le _
  have hqpow1 : 1 ≤ (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) := Real.one_le_rpow hq1 (by linarith)
  have hqpow0 : 0 ≤ (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) := Real.rpow_nonneg hq0 _
  have hcard := card_gradLabels_le hK (by linarith : (0 : ℝ) ≤ γ)
  have hT0 : 0 ≤ Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1))) :=
    mul_nonneg hZb (mul_nonneg hCb (mul_nonneg (by positivity) hqpow0))
  have hNs0 : 0 ≤ (N : ℝ) ^ (-s) := Real.rpow_nonneg hNpos.le _
  -- the pair part
  have hA0 : (N : ℝ) ^ (-s) * |∑ i ∈ gradLabels N ℓ γ, ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
        gradKernelH s (gradSep N ℓ γ X i j)| ≤
      ((gradLabels N ℓ γ).card : ℝ) * (((gradLabels N ℓ γ).card : ℝ) *
        (Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1))))) :=
    loopSum_abs_le hNs0 hT0 (fun i hi j hj => loopPair_term_bound hs0 hs1 hCb hZb hb1 hb2 hZ hγ
      hε0 hεs hℓ hK hev hi (Finset.mem_of_mem_erase hj))
  -- the background part
  obtain ⟨R, hR0, hNR, hbg⟩ := loopBackground_uniform hs0 hs1 hCb hZb hb1 hZ hγ hεs hℓ hK hev hX
  have hB0 : 0 ≤ Zb * Cb * (2 * R ^ (1 - s) / (1 - s)) :=
    mul_nonneg (mul_nonneg hZb hCb)
      (div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hR0 _)) (by linarith))
  have hB : |2 * (N : ℝ) ^ (1 - s) * ∑ i ∈ gradLabels N ℓ γ, gradBackground s ψ N ℓ γ (gradLift N X i)| ≤
      2 * (N : ℝ) ^ (1 - s) * (((gradLabels N ℓ γ).card : ℝ) *
        (Zb * Cb * (2 * R ^ (1 - s) / (1 - s)))) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Real.rpow_nonneg hNpos.le _)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |∑ i ∈ gradLabels N ℓ γ, gradBackground s ψ N ℓ γ (gradLift N X i)|
        ≤ ∑ i ∈ gradLabels N ℓ γ, |gradBackground s ψ N ℓ γ (gradLift N X i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ gradLabels N ℓ γ, Zb * Cb * (2 * R ^ (1 - s) / (1 - s)) :=
          Finset.sum_le_sum (fun i hi => hbg i hi)
      _ = ((gradLabels N ℓ γ).card : ℝ) * (Zb * Cb * (2 * R ^ (1 - s) / (1 - s))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the two parts together
  have hM0 : 0 ≤ gradM N ℓ γ := by linarith
  have hc0 : (0 : ℝ) ≤ ((gradLabels N ℓ γ).card : ℝ) := Nat.cast_nonneg _
  have hcoef : 0 ≤ 32 * gradM N ℓ γ * Zb * Cb / (1 - s) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hZb) hCb) (by linarith)
  have hA1 : |(N : ℝ) ^ (-s) * ∑ i ∈ gradLabels N ℓ γ, ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
        gradKernelH s (gradSep N ℓ γ X i j)| ≤
      ((gradLabels N ℓ γ).card : ℝ) * (((gradLabels N ℓ γ).card : ℝ) *
        (Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1))))) := by
    rw [abs_mul, abs_of_nonneg hNs0]
    exact hA0
  unfold gradLoop
  have hsplit := abs_sub ((N : ℝ) ^ (-s) * ∑ i ∈ gradLabels N ℓ γ, ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
        gradKernelH s (gradSep N ℓ γ X i j))
    (2 * (N : ℝ) ^ (1 - s) * ∑ i ∈ gradLabels N ℓ γ, gradBackground s ψ N ℓ γ (gradLift N X i))
  have hcardM : ((gradLabels N ℓ γ).card : ℝ) ≤ 8 * gradM N ℓ γ := hcard
  have hstep1 : ((gradLabels N ℓ γ).card : ℝ) * (((gradLabels N ℓ γ).card : ℝ) *
        (Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1))))) +
      2 * (N : ℝ) ^ (1 - s) * (((gradLabels N ℓ γ).card : ℝ) *
        (Zb * Cb * (2 * R ^ (1 - s) / (1 - s)))) ≤
      (8 * gradM N ℓ γ) * ((8 * gradM N ℓ γ) *
        (Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1))))) +
      2 * (N : ℝ) ^ (1 - s) * ((8 * gradM N ℓ γ) *
        (Zb * Cb * (2 * R ^ (1 - s) / (1 - s)))) := by
    refine add_le_add ?_ ?_
    · exact mul_le_mul hcardM (mul_le_mul_of_nonneg_right hcardM hT0) (mul_nonneg hc0 hT0)
        (by linarith)
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hcardM (mul_nonneg (mul_nonneg hZb hCb)
        (div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hR0 _)) (by linarith)))
  have hstep2 : (8 * gradM N ℓ γ) * ((8 * gradM N ℓ γ) *
        (Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1))))) +
      2 * (N : ℝ) ^ (1 - s) * ((8 * gradM N ℓ γ) *
        (Zb * Cb * (2 * R ^ (1 - s) / (1 - s)))) =
      64 * gradM N ℓ γ ^ 2 * (Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1)))) +
        32 * gradM N ℓ γ * Zb * Cb / (1 - s) * ((N : ℝ) ^ (1 - s) * R ^ (1 - s)) := by
    ring
  have hstep3 : 32 * gradM N ℓ γ * Zb * Cb / (1 - s) * ((N : ℝ) ^ (1 - s) * R ^ (1 - s)) ≤
      32 * gradM N ℓ γ * Zb * Cb / (1 - s) * (8 * gradM N ℓ γ) :=
    mul_le_mul_of_nonneg_left hNR hcoef
  have h8 : 32 * gradM N ℓ γ * Zb * Cb / (1 - s) * (8 * gradM N ℓ γ) =
      256 * gradM N ℓ γ ^ 2 * Zb * Cb / (1 - s) := by
    ring
  have hstep4 : 256 * gradM N ℓ γ ^ 2 * Zb * Cb / (1 - s) ≤
      256 * gradM N ℓ γ ^ 2 * Zb * Cb * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) / (1 - s) :=
    div_le_div_of_nonneg_right
      (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by positivity) hZb) hCb) hqpow1)
      (by linarith)
  have hfinal : Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Zb * gradM N ℓ γ ^ 2 *
      (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) =
      64 * gradM N ℓ γ ^ 2 * (Zb * (Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1)))) +
        256 * gradM N ℓ γ ^ 2 * Zb * Cb * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) / (1 - s) := by
    ring
  linarith [hsplit, add_le_add hA1 hB, hstep1, hstep2, hstep3, h8, hstep4, hfinal]

/-- The cutoff part of Lemma 5.8, the clause `|F^*_γ| ≤ C C_0 K^{B_1}`. The constants
depend only on `s`, `α`, `γ`, `ε` and `χ`. The bound holds for every `N ≥ 2`, every `ℓ > 0` with
`K = Nℓ ≥ 1`, every smooth `ψ` on `ℓ^{-1}𝕋` with the derivative envelopes of constant `C_0`, and
every anchored configuration `y` of the ordered domain (with `y_0 = 0`). The function
`F^*_γ = η H_γ[ψ_γ]` vanishes where `η = 0`. -/
theorem loopCutoffF_bound {s α γ ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα : s - 1 ≤ α)
    (hα2 : α < s / 2) (hγ : 1 < γ) (hε0 : 0 < ε) (hεs : ε ≤ 1 - s / 2) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C B : ℝ, 0 ≤ C ∧ ∀ (C0 : ℝ) (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ) (y : Fin (N : ℕ) → ℝ),
      0 ≤ C0 → 2 ≤ (N : ℕ) → 0 < ℓ → 1 ≤ (N : ℝ) * ℓ → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      y ∈ orderedDomain N → y ⟨0, N.pos⟩ = 0 →
      |loopCutoffF χ s γ ε N ℓ ψ y| ≤ C * C0 * ((N : ℝ) * ℓ) ^ B := by
  obtain ⟨Cenv, hCenv0, henv⟩ := loopTransport_envelope hs0 hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  obtain ⟨Cb, hCb, hb1, hb2⟩ := gradKernelH_bound hs0 hs1
  have hC : 0 ≤ Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Cenv := by
    have h1 : (0 : ℝ) ≤ 256 / (1 - s) := div_nonneg (by norm_num) (by linarith)
    have h2 : (0 : ℝ) ≤ 64 * 2 ^ (s + 1) + 256 / (1 - s) :=
      add_nonneg (by positivity) h1
    exact mul_nonneg (mul_nonneg hCb.le h2) hCenv0
  refine ⟨Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Cenv,
    (1 - s + α) + 2 * γ + ε * (s + 1), hC, ?_⟩
  intro C0 N ℓ ψ y hC0 _hN2 hℓ hK hψ hper hd1 hd2 hy hy0
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have ha0 : 0 ≤ 1 - s + α := by linarith
  have hZ0 : 0 ≤ Cenv * C0 := mul_nonneg hCenv0 hC0
  have hZb0 : 0 ≤ Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) :=
    mul_nonneg hZ0 (Real.rpow_nonneg hK0.le _)
  -- the uniform divided-difference bound on the transport
  have hZ' : ∀ t, |deriv (loopTransport χ N ℓ γ ψ) t| ≤
      Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) := by
    intro t
    have h := (henv N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hper hd1 hd2 t).1
    exact le_trans h (mul_le_mul_of_nonneg_left (gradWeightOne_le_rpow hs1 hK ha0) hZ0)
  have hZ : ∀ x y' : ℝ, |gradZ (loopTransport χ N ℓ γ ψ) ℓ x y'| ≤
      Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) :=
    fun x y' => gradZ_abs_le_const hZ'
  unfold loopCutoffF
  obtain ⟨hη0, hη1⟩ := loopCutoff_mem_Icc s γ ε ℓ y
  rcases eq_or_lt_of_le hη0 with h0 | hpos
  · rw [← h0, zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg hC hC0) (Real.rpow_nonneg hK0.le _)
  · have hev := gradEvent_of_loopCutoff_pos hℓ (⟨y, hy⟩ : Configuration N) hpos
    have hL := loopGradLoop_bound (ψ := loopTransport χ N ℓ γ ψ)
      (Zb := Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) hs0 hs1 hCb.le hZb0 hb1 hb2 hZ
      hγ.le hε0 hεs hℓ hK hev hy0
    have hη : |loopCutoff s γ ε N ℓ y| ≤ 1 := by
      rw [abs_of_nonneg hη0]
      exact hη1
    have hmul : |loopCutoff s γ ε N ℓ y * gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ y| ≤
        |gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ y| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hη
    have e1 : gradM N ℓ γ ^ 2 = ((N : ℝ) * ℓ) ^ (2 * γ) := by
      unfold gradM
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
      congr 1
      push_cast
      ring
    have e2 : (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) = ((N : ℝ) * ℓ) ^ (ε * (s + 1)) :=
      (Real.rpow_mul hK0.le ε (s + 1)).symm
    have e3 : ((N : ℝ) * ℓ) ^ (1 - s + α) * ((N : ℝ) * ℓ) ^ (2 * γ) *
        ((N : ℝ) * ℓ) ^ (ε * (s + 1)) =
        ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ + ε * (s + 1)) := by
      rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
    have heq : Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) *
        (Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) * gradM N ℓ γ ^ 2 *
        (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) =
        Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Cenv * C0 *
          ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ + ε * (s + 1)) := by
      rw [e1, e2, ← e3]
      ring
    calc |loopCutoff s γ ε N ℓ y * gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ y|
        ≤ |gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ y| := hmul
      _ ≤ Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) *
            (Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) * gradM N ℓ γ ^ 2 *
            (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) := hL
      _ = Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Cenv * C0 *
            ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ + ε * (s + 1)) := heq

end

end Riesz1
