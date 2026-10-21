/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffKernel
public import Riesz1.Auxiliary.LoopCutoffArcs
public import Riesz1.Auxiliary.GradientSplittingDifferences
public import Riesz1.Auxiliary.GradientSplittingWindowDefs

/-!
# The pair terms of the localized loop under the good event

The cutoff part of Lemma 5.8, the bound `|F^*_γ| ≤ C C_0 K^{B_1}`. Here `K = Nℓ`,
`M = K^γ` and `K^ε` is the cutoff scale. On the good event, every pair term of the loop satisfies

  `N^{-s} |h(r)| ≤ C_h (2 K^ε)^{s+1}`, where `r = x_{i+k} - x_i` and `h = gradKernelH s`.

The proof has three cases. A separation `|r| ≤ 3/4` uses the bound `C |r|^{-s}` together with
`N |r| ≥ (K^ε)^{-1}` (the arc lower bound). In a partial window `|r| ≤ 1/2` always holds. In a full
window a separation `|r| > 3/4` lies at distance at least `(K^ε)^{-1}/2` from `1` (the
complementary arc), so the singularity `(1 - r)^{-s-1}` contributes a factor `(K^ε)^{s+1}`.
-/

@[expose] public section

open Finset

namespace Riesz1

noncomputable section

/-- The weight `w_1` is at most `K ^ a` when `K ≥ 1` and `a ≥ 0`. -/
lemma gradWeightOne_le_rpow {s a K L u : ℝ} (hs1 : s < 1) (hK : 1 ≤ K) (ha : 0 ≤ a) :
    gradWeightOne s a K L u ≤ K ^ a := by
  have hK0 : 0 < K := by linarith
  unfold gradWeightOne
  split_ifs with h
  · have hm : K⁻¹ ≤ max (circDist L u) K⁻¹ := le_max_right _ _
    calc max (circDist L u) K⁻¹ ^ (-a) ≤ K⁻¹ ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hK0) hm (by linarith)
      _ = K ^ a := by rw [Real.inv_rpow hK0.le, Real.rpow_neg hK0.le, inv_inv]
  · have h1 : 1 ≤ circDist L u := not_lt.mp h
    calc circDist L u ^ (s - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
      _ ≤ K ^ a := Real.one_le_rpow hK ha

/-- A uniform bound for the divided difference: `|Z(x,y)| ≤ M` once `|ψ'| ≤ M` everywhere. -/
lemma gradZ_abs_le_const {ψ : ℝ → ℝ} {ℓ x y M : ℝ} (hM : ∀ t, |deriv ψ t| ≤ M) :
    |gradZ ψ ℓ x y| ≤ M := by
  unfold gradZ
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun θ : ℝ => deriv ψ ((x + θ * (y - x)) / ℓ)) (C := M)
    (fun θ _ => by rw [Real.norm_eq_abs]; exact hM _)
  simpa [Real.norm_eq_abs] using h

/-- Small separations. If `|v| ≤ C |r| ^ (-s)` and `q^{-1} ≤ N |r|`, then `N^{-s} |v| ≤ C q^s`. -/
lemma loopKernel_small_scaled {r v N q Cb s : ℝ} (hN : 0 < N) (hq : 1 ≤ q) (hs0 : 0 ≤ s)
    (hCb : 0 ≤ Cb) (hv : |v| ≤ Cb * |r| ^ (-s)) (hc : q⁻¹ ≤ N * |r|) :
    N ^ (-s) * |v| ≤ Cb * q ^ s := by
  have hq0 : 0 < q := by linarith
  have hmono : (N * |r|) ^ (-s) ≤ (q⁻¹) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hq0) hc (by linarith)
  have hsplit : (N * |r|) ^ (-s) = N ^ (-s) * |r| ^ (-s) := Real.mul_rpow hN.le (abs_nonneg r)
  have hinv : (q⁻¹) ^ (-s) = q ^ s := by
    rw [Real.inv_rpow hq0.le, Real.rpow_neg hq0.le, inv_inv]
  calc N ^ (-s) * |v| ≤ N ^ (-s) * (Cb * |r| ^ (-s)) :=
        mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg hN.le _)
    _ = Cb * (N * |r|) ^ (-s) := by rw [hsplit]; ring
    _ ≤ Cb * (q⁻¹) ^ (-s) := mul_le_mul_of_nonneg_left hmono hCb
    _ = Cb * q ^ s := by rw [hinv]

/-- Near-one separations. If `|v| ≤ C (1 - |r|) ^ (-s - 1)` and `q^{-1}/2 ≤ 1 - |r|`, then
`N^{-s} |v| ≤ C (2 q)^{s+1}`. -/
lemma loopKernel_near_scaled {r v N q Cb s : ℝ} (hN : 1 ≤ N) (hq : 1 ≤ q) (hs0 : 0 ≤ s)
    (hCb : 0 ≤ Cb) (hv : |v| ≤ Cb * (1 - |r|) ^ (-s - 1)) (hd : q⁻¹ / 2 ≤ 1 - |r|) :
    N ^ (-s) * |v| ≤ Cb * (2 ^ (s + 1) * q ^ (s + 1)) := by
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < q⁻¹ / 2 := by positivity
  have hN0 : N ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hmono : (1 - |r|) ^ (-s - 1) ≤ (q⁻¹ / 2) ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos hd0 hd (by linarith)
  have hval : (q⁻¹ / 2) ^ (-s - 1) = 2 ^ (s + 1) * q ^ (s + 1) := by
    have e1 : q⁻¹ / 2 = (2 * q)⁻¹ := by
      rw [mul_inv]
      ring
    have e2 : -s - 1 = -(s + 1) := by ring
    rw [e1, e2, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      Real.mul_rpow (by norm_num) hq0.le]
  have h3 : |v| ≤ Cb * (q⁻¹ / 2) ^ (-s - 1) :=
    le_trans hv (mul_le_mul_of_nonneg_left hmono hCb)
  calc N ^ (-s) * |v| ≤ 1 * |v| := mul_le_mul_of_nonneg_right hN0 (abs_nonneg v)
    _ ≤ Cb * (q⁻¹ / 2) ^ (-s - 1) := by rw [one_mul]; exact h3
    _ = Cb * (2 ^ (s + 1) * q ^ (s + 1)) := by rw [hval]

/-- The rpow estimate behind the partial-window separation bound: for `0 ≤ t ≤ 2 K^γ` and
`ε ≤ 1 - s/2`, one has `K^ε t^{s/2} ≤ 2 K^γ`. -/
lemma loopRpow_mul_le {s γ ε K t : ℝ} (hK : 1 ≤ K) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hγ : 1 ≤ γ)
    (hε : ε ≤ 1 - s / 2) (ht0 : 0 ≤ t) (ht : t ≤ 2 * K ^ γ) :
    K ^ ε * t ^ (s / 2) ≤ 2 * K ^ γ := by
  have hK0 : 0 < K := by linarith
  have hM0 : 0 ≤ K ^ γ := Real.rpow_nonneg hK0.le _
  have h1 : t ^ (s / 2) ≤ (2 * K ^ γ) ^ (s / 2) := Real.rpow_le_rpow ht0 ht (by linarith)
  have h2 : (2 * K ^ γ) ^ (s / 2) = 2 ^ (s / 2) * (K ^ γ) ^ (s / 2) :=
    Real.mul_rpow (by norm_num) hM0
  have h3 : (2 : ℝ) ^ (s / 2) ≤ 2 := by
    calc (2 : ℝ) ^ (s / 2) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h4 : (K ^ γ) ^ (s / 2) = K ^ (γ * (s / 2)) := (Real.rpow_mul hK0.le γ (s / 2)).symm
  have hpow : 0 ≤ (K ^ γ) ^ (s / 2) := Real.rpow_nonneg hM0 _
  have h5 : K ^ ε * K ^ (γ * (s / 2)) = K ^ (ε + γ * (s / 2)) := (Real.rpow_add hK0 _ _).symm
  have hγs : 0 ≤ (γ - 1) * (1 - s / 2) := mul_nonneg (by linarith) (by linarith)
  have h6 : K ^ (ε + γ * (s / 2)) ≤ K ^ γ :=
    Real.rpow_le_rpow_of_exponent_le hK (by nlinarith [hγs])
  have ht' : t ^ (s / 2) ≤ 2 * (K ^ γ) ^ (s / 2) := by
    calc t ^ (s / 2) ≤ 2 ^ (s / 2) * (K ^ γ) ^ (s / 2) := h2 ▸ h1
      _ ≤ 2 * (K ^ γ) ^ (s / 2) := mul_le_mul_of_nonneg_right h3 hpow
  have hKε : 0 ≤ K ^ ε := Real.rpow_nonneg hK0.le _
  calc K ^ ε * t ^ (s / 2) ≤ K ^ ε * (2 * (K ^ γ) ^ (s / 2)) :=
        mul_le_mul_of_nonneg_left ht' hKε
    _ = 2 * K ^ (ε + γ * (s / 2)) := by rw [h4, ← h5]; ring
    _ ≤ 2 * K ^ γ := mul_le_mul_of_nonneg_left h6 (by norm_num)

/-- In a partial window, `M < N/8` makes the scaled separation of a pair of window labels at most
`N/2`, under the good event. -/
lemma loopPartial_sep_le {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hγ : 1 ≤ γ) (hεs : ε ≤ 1 - s / 2) (hℓ : 0 < ℓ)
    (hK : 1 ≤ (N : ℝ) * ℓ) (hev : gradEvent s (2 * γ) ε N ℓ X) (i k : ℤ)
    (hP : GradPartial N ℓ γ) (hi : i ∈ gradLabels N ℓ γ ∧ i + k ∈ gradLabels N ℓ γ)
    (hk : 2 * |k| ≤ (N : ℤ)) :
    |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i)| ≤ (N : ℝ) / 2 := by
  have hM8 : gradM N ℓ γ < (N : ℝ) / 8 := hP
  -- the separation index is at most twice the window radius `M = K^γ`
  have hkR : |(k : ℝ)| ≤ 2 * gradM N ℓ γ := by
    have hfl := (mem_gradLabels_partial hP i).1 hi.1
    have hfl2 := (mem_gradLabels_partial hP (i + k)).1 hi.2
    have hab : |k| ≤ 2 * ⌊gradM N ℓ γ⌋ := abs_le.mpr ⟨by omega, by omega⟩
    have hR : ((|k| : ℤ) : ℝ) ≤ ((2 * ⌊gradM N ℓ γ⌋ : ℤ) : ℝ) := by exact_mod_cast hab
    rw [Int.cast_abs] at hR
    push_cast at hR
    have hfloor : (⌊gradM N ℓ γ⌋ : ℝ) ≤ gradM N ℓ γ := Int.floor_le _
    linarith
  have hev2 := gradEvent_pair_bound hev hℓ i k hk
    (loop_pair_window_two hK (by linarith) (Or.inr hi))
  have hKε : ((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2) ≤ 2 * gradM N ℓ γ :=
    loopRpow_mul_le hK hs0.le (by linarith) hγ hεs (abs_nonneg _) hkR
  have htri : |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i)| ≤
      |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| + |(k : ℝ)| := by
    have h := abs_add_le ((N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k) (k : ℝ)
    rwa [sub_add_cancel] at h
  linarith

/-- Full windows: if `γ` is full then so is `2γ`. -/
lemma not_partial_two_of_not_partial {ℓ γ : ℝ} {N : ℕ+} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (h : ¬GradPartial N ℓ γ) : ¬GradPartial N ℓ (2 * γ) := by
  intro h2
  have hMle : ((N : ℝ) * ℓ) ^ γ ≤ ((N : ℝ) * ℓ) ^ (2 * γ) :=
    Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  have h1 : (N : ℝ) / 8 ≤ ((N : ℝ) * ℓ) ^ γ := not_lt.mp h
  have h2' : ((N : ℝ) * ℓ) ^ (2 * γ) < (N : ℝ) / 8 := h2
  linarith

/-- The good event bounds one pair term of the localized loop. For a pair of labels `i` and
`i + k` of the window `γ`, with `2|k| ≤ N` and `K^ε` the cutoff scale,
`N^{-s} |h(x_{i+k} - x_i)| ≤ C_h (2 K^ε)^{s+1}`. -/
lemma loopPair_kernel_bound {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {Cb : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hCb : 0 ≤ Cb)
    (hb1 : ∀ r : ℝ, |r| ≤ 3 / 4 → |gradKernelH s r| ≤ Cb * |r| ^ (-s))
    (hb2 : ∀ r : ℝ, 3 / 4 < r → r < 1 → |gradKernelH s r| ≤ Cb * (1 - r) ^ (-s - 1))
    (hγ : 1 ≤ γ) (hε0 : 0 < ε) (hεs : ε ≤ 1 - s / 2) (hℓ : 0 < ℓ)
    (hK : 1 ≤ (N : ℝ) * ℓ) (hev : gradEvent s (2 * γ) ε N ℓ X) (i k : ℤ)
    (hk : 2 * |k| ≤ (N : ℤ))
    (hi : ¬GradPartial N ℓ γ ∨ (i ∈ gradLabels N ℓ γ ∧ i + k ∈ gradLabels N ℓ γ)) :
    (N : ℝ) ^ (-s) * |gradKernelH s (gradLift N X (i + k) - gradLift N X i)| ≤
      Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1)) := by
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr N.pos
  have hq1 : 1 ≤ ((N : ℝ) * ℓ) ^ ε := Real.one_le_rpow hK hε0.le
  have hq0 : 0 < ((N : ℝ) * ℓ) ^ ε := by linarith
  have hqinv : 0 < (((N : ℝ) * ℓ) ^ ε)⁻¹ := inv_pos.mpr hq0
  have hRHS : 0 ≤ Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1)) :=
    mul_nonneg hCb (mul_nonneg (by positivity) (Real.rpow_nonneg hq0.le _))
  have hi2 := loop_pair_window_two hK (by linarith) hi
  have hlow := gradEvent_sep_lower hev i k hi2
  rw [Real.rpow_neg hK0.le] at hlow
  by_cases hk0 : k = 0
  · subst hk0
    have hr0 : gradLift N X (i + 0) - gradLift N X i = 0 := by simp
    rw [hr0]
    simpa [gradKernelH] using hRHS
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have h := Int.one_le_abs hk0
      have h' : ((1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h
      rw [Int.cast_abs] at h'
      simpa using h'
    have hc : (((N : ℝ) * ℓ) ^ ε)⁻¹ ≤ (N : ℝ) * |gradLift N X (i + k) - gradLift N X i| := by
      calc (((N : ℝ) * ℓ) ^ ε)⁻¹ = (((N : ℝ) * ℓ) ^ ε)⁻¹ * 1 := (mul_one _).symm
        _ ≤ (((N : ℝ) * ℓ) ^ ε)⁻¹ * |(k : ℝ)| := mul_le_mul_of_nonneg_left hk1 hqinv.le
        _ ≤ |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i)| := hlow
        _ = (N : ℝ) * |gradLift N X (i + k) - gradLift N X i| := by
          rw [abs_mul, abs_of_pos hNpos]
    have hqs : (((N : ℝ) * ℓ) ^ ε) ^ s ≤ 2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) := by
      have h1 : (((N : ℝ) * ℓ) ^ ε) ^ s ≤ (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      have h2 : (1 : ℝ) ≤ 2 ^ (s + 1) := Real.one_le_rpow (by norm_num) (by linarith)
      have h3 : (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) ≤ 2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) :=
        le_mul_of_one_le_left (Real.rpow_nonneg hq0.le _) h2
      linarith
    set r := gradLift N X (i + k) - gradLift N X i with hr
    by_cases hr3 : |r| ≤ 3 / 4
    · have h := loopKernel_small_scaled (v := gradKernelH s r) hNpos hq1 hs0.le hCb
        (hb1 r hr3) hc
      calc (N : ℝ) ^ (-s) * |gradKernelH s r| ≤ Cb * (((N : ℝ) * ℓ) ^ ε) ^ s := h
        _ ≤ Cb * (2 ^ (s + 1) * (((N : ℝ) * ℓ) ^ ε) ^ (s + 1)) :=
          mul_le_mul_of_nonneg_left hqs hCb
    · -- a separation above `3/4` forces a full window, since partial separations are below `1/2`
      have hfull : ¬GradPartial N ℓ γ := by
        intro hP
        have hsep := loopPartial_sep_le hs0 hs1 hγ hεs hℓ hK hev i k hP
          (hi.resolve_left (fun h => absurd hP h)) hk
        rw [← hr, abs_mul, abs_of_pos hNpos] at hsep
        have h12 : |r| ≤ 1 / 2 := le_of_mul_le_mul_left (by linarith [hsep]) hNpos
        exact hr3 (by linarith [h12])
      have hkR' : 2 * |(k : ℝ)| ≤ (N : ℝ) := by
        have h := (Int.cast_le (R := ℝ)).mpr hk
        push_cast at h
        linarith
      have hcomp := gradEvent_sep_complement hev hℓ
        (not_partial_two_of_not_partial hK (by linarith) hfull) i k
        (by linarith [abs_nonneg k])
      rw [Real.rpow_neg hK0.le, ← hr] at hcomp
      have hkN : (N : ℝ) / 2 ≤ (N : ℝ) - |(k : ℝ)| := by linarith
      have h1 : (((N : ℝ) * ℓ) ^ ε)⁻¹ * ((N : ℝ) / 2) ≤
          (((N : ℝ) * ℓ) ^ ε)⁻¹ * ((N : ℝ) - |(k : ℝ)|) :=
        mul_le_mul_of_nonneg_left hkN hqinv.le
      have h2 : (N : ℝ) * ((((N : ℝ) * ℓ) ^ ε)⁻¹ / 2) ≤ (N : ℝ) * (1 - |r|) := by
        linarith [h1, hcomp]
      have hd : (((N : ℝ) * ℓ) ^ ε)⁻¹ / 2 ≤ 1 - |r| := le_of_mul_le_mul_left h2 hNpos
      have hd0 : 0 < (((N : ℝ) * ℓ) ^ ε)⁻¹ / 2 := by linarith
      rcases le_or_gt 0 r with hr0 | hr0
      · have habs : |r| = r := abs_of_nonneg hr0
        have hgt : 3 / 4 < r := by linarith [not_le.mp hr3]
        have hlt : r < 1 := by linarith
        have hv : |gradKernelH s r| ≤ Cb * (1 - |r|) ^ (-s - 1) := by
          rw [habs]
          exact hb2 r hgt hlt
        exact loopKernel_near_scaled hN1 hq1 hs0.le hCb hv hd
      · have habs : |r| = -r := abs_of_neg hr0
        have hgt : 3 / 4 < -r := by linarith [not_le.mp hr3]
        have hlt : -r < 1 := by linarith
        have hv : |gradKernelH s r| ≤ Cb * (1 - |r|) ^ (-s - 1) := by
          have h := hb2 (-r) hgt hlt
          rw [gradSplit_gradKernelH_even s r] at h
          rw [habs]
          exact h
        exact loopKernel_near_scaled hN1 hq1 hs0.le hCb hv hd

/-- The number of labels of a window is at most `8 M`, with `M = K^γ`. -/
lemma card_gradLabels_le {ℓ γ : ℝ} {N : ℕ+} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ) :
    ((gradLabels N ℓ γ).card : ℝ) ≤ 8 * gradM N ℓ γ := by
  have hM1 : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  unfold gradLabels
  by_cases hP : GradPartial N ℓ γ
  · simp only [hP, ↓reduceIte, Int.card_Icc]
    have hfl0 : 0 ≤ ⌊gradM N ℓ γ⌋ := Int.floor_nonneg.mpr (by linarith)
    have hfl : (⌊gradM N ℓ γ⌋ : ℝ) ≤ gradM N ℓ γ := Int.floor_le _
    have h1 : ((⌊gradM N ℓ γ⌋ + 1 - -⌊gradM N ℓ γ⌋).toNat : ℤ) = 2 * ⌊gradM N ℓ γ⌋ + 1 := by
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have h2 : (((⌊gradM N ℓ γ⌋ + 1 - -⌊gradM N ℓ γ⌋).toNat : ℕ) : ℝ) =
        ((2 * ⌊gradM N ℓ γ⌋ + 1 : ℤ) : ℝ) := by
      rw [← h1, Int.cast_natCast]
    rw [h2]
    push_cast
    linarith
  · simp only [hP, ↓reduceIte, Int.card_Ico]
    have hN : (N : ℝ) ≤ 8 * gradM N ℓ γ := by
      have := not_lt.mp hP
      linarith
    have hc : (((N : ℤ) - 0).toNat : ℝ) = (N : ℝ) := by simp
    rw [hc]
    exact hN

/-- The increment of a path is `k = j - i` in a partial window. In a full window it
satisfies `|k| ≤ N/2`. Both pairs `i` and `i + k` remain labels of the window. -/
lemma loopPathIncr_spec {ℓ γ : ℝ} {N : ℕ+} {i j : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) :
    2 * |gradPathIncr N ℓ γ i j| ≤ (N : ℤ) ∧
      (¬GradPartial N ℓ γ ∨ (i ∈ gradLabels N ℓ γ ∧ i + gradPathIncr N ℓ γ i j ∈ gradLabels N ℓ γ)) := by
  by_cases hP : GradPartial N ℓ γ
  · have hfl := (mem_gradLabels_partial hP i).1 hi
    have hfl2 := (mem_gradLabels_partial hP j).1 hj
    have hM8 : gradM N ℓ γ < (N : ℝ) / 8 := hP
    have hfl0 : (⌊gradM N ℓ γ⌋ : ℝ) ≤ gradM N ℓ γ := Int.floor_le _
    have hint : 8 * ⌊gradM N ℓ γ⌋ < (N : ℤ) := by
      have : (8 * ⌊gradM N ℓ γ⌋ : ℝ) < (N : ℝ) := by linarith
      exact_mod_cast this
    have hk : gradPathIncr N ℓ γ i j = j - i := by
      unfold gradPathIncr
      simp only [hP, ↓reduceIte]
    rw [hk]
    refine ⟨?_, Or.inr ⟨hi, ?_⟩⟩
    · have hab : |j - i| ≤ 2 * ⌊gradM N ℓ γ⌋ := abs_le.mpr ⟨by omega, by omega⟩
      linarith
    · rw [show i + (j - i) = j by ring]
      exact hj
  · refine ⟨?_, Or.inl hP⟩
    unfold gradPathIncr
    simp only [hP, ↓reduceIte]
    have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast N.pos
    have ht0 : 0 ≤ (j - i) % (N : ℤ) := Int.emod_nonneg _ hNpos.ne'
    have htN : (j - i) % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos _ hNpos
    generalize (j - i) % (N : ℤ) = t at ht0 htN ⊢
    split_ifs with h1 h2 h3
    · rw [abs_of_nonneg ht0]
      omega
    · rw [abs_of_nonpos (by omega : t - (N : ℤ) ≤ 0)]
      omega
    · rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (N : ℤ) / 2)]
      omega
    · rw [abs_neg, abs_of_nonneg (by omega : (0 : ℤ) ≤ (N : ℤ) / 2)]
      omega

end

end Riesz1

end
