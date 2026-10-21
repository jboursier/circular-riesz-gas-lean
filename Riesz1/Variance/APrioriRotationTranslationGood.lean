/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationTranslationPoint
public import Riesz1.Variance.APrioriRotationTranslationLabels
public import Riesz1.Variance.APrioriRotationTranslationSum
public import Riesz1.Variance.APrioriRotationVariance

/-!
# The translation error on the good event

Lemma 5.2, translation error, deterministic part. On the good event
`𝒜_{ε,γ}`, the window labels satisfy the comparisons of
`aPrioriGood_deterministic`, and the translation error is bounded by a power of `K = N ℓ`:

`|Δ_D(y)| ≤ C K^{λ + (3 + λ) ε}` for `0 ≤ D ≤ K^ε`,

where `y` is the anchored vector of a configuration on the good event, and `C` depends only on
`s, γ, λ, ε`.

For a window label `i` with label distance `d_i` from the origin label, the comparisons give
`K^{-ε} d_i ≤ a_i ≤ 2 K^ε d_i`, where `a_i = N dist(1, y_i)` is the microscopic distance. Labels
with `a_i < 2K^ε` are few, since they have `d_i ≤ 2 K^{2ε}`. Every other label is far from the
origin, and its derivative majorant is bounded by a power of `d_i`. Summing over the window, the
two power sums of `Riesz1.sum_Icc_min_rpow_le` and `Riesz1.sum_Icc_inv_le` give the bound.
-/

@[expose] public section

open Finset

namespace Riesz1

/-- The constant of the good-event translation bound. -/
noncomputable def goodConst (s γ lam ε : ℝ) : ℝ :=
  10 + 2 ^ (2 + lam) * (1 + Real.log 4 + γ / ε) + 2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1))

/-- The derivative majorant is at most `K^{1+λ} + 1` on `[0, ∞)`. -/
theorem derivMajorant_le_near {K lam s t : ℝ} (hK : 0 < K) (hlam : 0 ≤ lam) (hs : s < 1)
    (ht : 0 ≤ t) : derivMajorant K lam s t ≤ K ^ (1 + lam) + 1 := by
  have hanti : derivMajorant K lam s t ≤ derivMajorant K lam s 0 :=
    derivMajorant_antitoneOn hK hlam (by linarith : s < 3) (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  refine hanti.trans ?_
  unfold derivMajorant
  have hz : max (0 : ℝ) K⁻¹ = K⁻¹ := max_eq_right (inv_nonneg.2 hK.le)
  have hz2 : max (0 : ℝ) 2 = 2 := max_eq_right (by norm_num)
  rw [hz, hz2, Real.inv_rpow hK.le, one_div, inv_inv]
  have h2 : (1 : ℝ) ≤ 2 ^ (3 - s) := Real.one_le_rpow (by norm_num) (by linarith)
  have h3 : 1 / (2 : ℝ) ^ (3 - s) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact h2
  linarith

/-- **Far-term pointwise bound.** Let `K > 0`, `d ≥ 1`, and let the microscopic distance `a > 0`
satisfy `K^{-ε} d ≤ a`. If the argument `t` satisfies `a / (2K) ≤ t`, then the derivative
majorant at `t` is at most `(2 K^{1+ε}/d)^{1+λ} + min(2 K^{1+ε}/d, 1/2)^{3-s}`. -/
theorem derivMajorant_far_le {K ε lam s t a d : ℝ} (hK : 0 < K) (hlam : 0 ≤ lam)
    (hs : s < 1) (hd : 1 ≤ d) (ha : 0 < a) (hadK : K ^ (-ε) * d ≤ a) (ht : a / (2 * K) ≤ t) :
    derivMajorant K lam s t ≤
      (2 * K ^ (1 + ε) / d) ^ (1 + lam) + min (2 * K ^ (1 + ε) / d) (1 / 2) ^ (3 - s) := by
  have hd0 : 0 < d := by linarith
  have hq0 : 0 < a / (2 * K) := div_pos ha (by linarith)
  have ht0 : 0 < t := lt_of_lt_of_le hq0 ht
  set r : ℝ := 2 * K ^ (1 + ε) / d with hr_def
  -- The comparison `2K/a ≤ r`, from `K^{-ε} d ≤ a`.
  have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK ε
  have hdε : d ≤ K ^ ε * a := by
    have h1 : K ^ (-ε) * d * K ^ ε = d := by
      rw [Real.rpow_neg hK.le, inv_mul_eq_div, div_mul_cancel₀ _ hKε.ne']
    have h2 : K ^ (-ε) * d * K ^ ε ≤ a * K ^ ε := mul_le_mul_of_nonneg_right hadK hKε.le
    nlinarith
  have hinv : 1 / (a / (2 * K)) ≤ r := by
    rw [hr_def, one_div_div, div_le_div_iff₀ ha hd0, show K ^ (1 + ε) = K * K ^ ε by
      rw [Real.rpow_add hK, Real.rpow_one, mul_comm]]
    nlinarith
  unfold derivMajorant
  have hA : 1 / (max t K⁻¹) ^ (1 + lam) ≤ r ^ (1 + lam) := by
    have hmax : a / (2 * K) ≤ max t K⁻¹ := le_trans ht (le_max_left _ _)
    have hpos : 0 < a / (2 * K) := hq0
    calc 1 / (max t K⁻¹) ^ (1 + lam)
        ≤ 1 / (a / (2 * K)) ^ (1 + lam) :=
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos hpos _)
            (Real.rpow_le_rpow hpos.le hmax (by linarith))
      _ = (1 / (a / (2 * K))) ^ (1 + lam) := by rw [Real.div_rpow zero_le_one hpos.le, Real.one_rpow]
      _ ≤ r ^ (1 + lam) := Real.rpow_le_rpow (by positivity) hinv (by linarith)
  have hB : 1 / (max t 2) ^ (3 - s) ≤ min r (1 / 2) ^ (3 - s) := by
    have hmax2 : (2 : ℝ) ≤ max t 2 := le_max_right _ _
    have hmaxpos : 0 < max t 2 := by linarith
    have hmin1 : 1 / (max t 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hmax2
    have hmin2 : 1 / (max t 2) ≤ r := by
      refine le_trans ?_ hinv
      refine one_div_le_one_div_of_le hq0 (le_trans ht (le_max_left _ _))
    have hmin : 1 / (max t 2) ≤ min r (1 / 2) := le_min hmin2 hmin1
    calc 1 / (max t 2) ^ (3 - s) = (1 / (max t 2)) ^ (3 - s) := by
          rw [Real.div_rpow zero_le_one hmaxpos.le, Real.one_rpow]
      _ ≤ min r (1 / 2) ^ (3 - s) :=
          Real.rpow_le_rpow (by positivity) hmin (by linarith)
  have hrmin : min (2 * K ^ (1 + ε) / d) (1 / 2) = min r (1 / 2) := rfl
  rw [hrmin]
  linarith

/-- **Power sum over distances.** For `X ≥ 0` and `λ ≥ 0`, the sum of `(X/d)^{1+λ}` over
`1 ≤ d ≤ M` is at most `X^{1+λ}(1 + log M)`. -/
theorem sum_Icc_rpow_div_le {X lam : ℝ} (hX : 0 ≤ X) (hlam : 0 ≤ lam) (M : ℕ) :
    ∑ d ∈ Finset.Icc 1 M, (X / (d : ℝ)) ^ (1 + lam) ≤ X ^ (1 + lam) * (1 + Real.log M) := by
  have hterm : ∀ d ∈ Finset.Icc 1 M, (X / (d : ℝ)) ^ (1 + lam) ≤ X ^ (1 + lam) * (1 / (d : ℝ)) := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.1 hd).1
    rw [Real.div_rpow hX (by linarith), mul_one_div]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hX _) (by linarith)
    calc (d : ℝ) = (d : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (d : ℝ) ^ (1 + lam) := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  calc ∑ d ∈ Finset.Icc 1 M, (X / (d : ℝ)) ^ (1 + lam)
      ≤ ∑ d ∈ Finset.Icc 1 M, X ^ (1 + lam) * (1 / (d : ℝ)) := Finset.sum_le_sum hterm
    _ = X ^ (1 + lam) * ∑ d ∈ Finset.Icc 1 M, (1 / (d : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ X ^ (1 + lam) * (1 + Real.log M) :=
        mul_le_mul_of_nonneg_left (sum_Icc_inv_le M) (Real.rpow_nonneg hX _)

/-- **Window labels on the good event.** For a window label `i` of the good event, with `a_i` the
microscopic distance `N dist(1, y_i)` of the anchored vector `y = rotAnchorVec N X`, the
comparisons give `K^{-ε} d(i, 1) ≤ a_i ≤ 2 K^ε d(i, 1)`. -/
theorem good_label_bounds {N : ℕ+} {s K γ ε : ℝ} (hs : 0 < s) (hs1 : s < 1) (hK : 1 ≤ K)
    (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (hεγ : ε ≤ γ * (1 - s / 2)) {X : Configuration N}
    (hX : X ∈ goodEvent N s K γ ε) {i : Fin (N : ℕ)} (hi : i ∈ window N K γ) :
    K ^ (-ε) * (labelDistToOne N i : ℝ) ≤ ((N : ℕ) : ℝ) * circDist 1 (rotAnchorVec N X i) ∧
      ((N : ℕ) : ℝ) * circDist 1 (rotAnchorVec N X i) ≤ 2 * K ^ ε * (labelDistToOne N i : ℝ) := by
  set o : Fin (N : ℕ) := ⟨0, N.pos⟩ with ho_def
  have ho : o ∈ window N K γ := origin_mem_window N hK
  have h0 : labelOf N 0 = o := by
    have := labelOf_natCast N o
    simpa using this
  have hcirc : circDist 1 (X.val i - X.val o) = circDist 1 (rotAnchorVec N X i) := by
    have hi' : labelOf N ((i : ℕ) : ℤ) = i := labelOf_natCast N i
    have := APG.circDist_labels X o i (a := 0) (b := ((i : ℕ) : ℤ)) h0 hi'
    simpa [rotAnchorVec] using this
  have hd : cyclicIndexDistance N o i = labelDistToOne N i := by
    unfold labelDistToOne
    exact cyclicIndexDistance_comm' N o i
  have hlow := APG.lower_comparison X hs hs1 hK hγ hεγ hX ho hi
  have hup := APG.upper_comparison X hs1 hK hε hX ho hi
  rw [hd, hcirc] at hlow hup
  exact ⟨hlow, hup⟩

/-- **Power bound of the good-event sum.** The bound on the window sum, with the power sums of the
far and near labels, is at most `goodConst` times `K^{λ + (3 + λ) ε}`, after the factor `K^ε/K`
of the translation error. -/
theorem translation_power_bound {K s γ lam ε : ℝ} (M : ℕ) (hK1 : 1 ≤ K) (hs1 : s < 1)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) (hε : 0 < ε)
    (hM : (M : ℝ) ≤ 4 * K ^ γ) (hM1 : (1 : ℝ) ≤ M) :
    K ^ ε / K * ((4 * (K ^ ε) ^ 2 + 1) * (K ^ (1 + lam) + 1) +
      2 * (2 * K ^ (1 + ε)) ^ (1 + lam) * (1 + Real.log M) +
      2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * K ^ (1 + ε)) ≤
    goodConst s γ lam ε * K ^ (lam + (3 + lam) * ε) := by
  have hK0 : 0 < K := by linarith
  have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK0 ε
  have hKε1 : 1 ≤ K ^ ε := Real.one_le_rpow hK1 hε.le
  have hE0 : 0 ≤ K ^ (lam + (3 + lam) * ε) := Real.rpow_nonneg hK0.le _
  -- The logarithm of the window count, `1 + log M ≤ c K^ε`.
  have hlogbd : 1 + Real.log M ≤ (1 + Real.log 4 + γ / ε) * K ^ ε := by
    have hlogM : Real.log M ≤ Real.log (4 * K ^ γ) :=
      Real.log_le_log (by linarith) hM
    have hlog4 : Real.log (4 * K ^ γ) = Real.log 4 + γ * Real.log K := by
      rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hK0 γ).ne', Real.log_rpow hK0]
    have hlogK : Real.log K ≤ K ^ ε / ε := Real.log_le_rpow_div hK0.le hε
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hγε : 0 ≤ γ / ε := div_nonneg (by linarith) hε.le
    have h1 : γ * Real.log K ≤ γ * (K ^ ε / ε) :=
      mul_le_mul_of_nonneg_left hlogK (by linarith)
    have h2 : (1 + Real.log 4) * 1 ≤ (1 + Real.log 4) * K ^ ε :=
      mul_le_mul_of_nonneg_left hKε1 (by linarith)
    have h3 : γ * (K ^ ε / ε) = (γ / ε) * K ^ ε := by ring
    have h4 : (1 + Real.log 4 + γ / ε) * K ^ ε = (1 + Real.log 4) * K ^ ε + (γ / ε) * K ^ ε := by
      ring
    linarith
  -- The three summands.
  have hT1 : K ^ ε / K * ((4 * (K ^ ε) ^ 2 + 1) * (K ^ (1 + lam) + 1)) ≤
      10 * K ^ (lam + (3 + lam) * ε) := by
    have hQ : 1 ≤ K ^ (1 + lam) := Real.one_le_rpow hK1 (by linarith)
    have hP2 : 1 ≤ (K ^ ε) ^ 2 := one_le_pow₀ hKε1
    have hA : (4 * (K ^ ε) ^ 2 + 1) * (K ^ (1 + lam) + 1) ≤
        10 * ((K ^ ε) ^ 2 * K ^ (1 + lam)) := by
      nlinarith
    have hE : K ^ ε / K * ((K ^ ε) ^ 2 * K ^ (1 + lam)) = K ^ (lam + 3 * ε) := by
      have h2 : (K ^ ε) ^ 2 = K ^ (2 * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
        congr 1
        push_cast
        ring
      rw [h2, ← Real.rpow_sub_one hK0.ne' ε, ← Real.rpow_add hK0, ← Real.rpow_add hK0]
      congr 1
      ring
    have hmono : K ^ (lam + 3 * ε) ≤ K ^ (lam + (3 + lam) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hK1 (by nlinarith)
    have hdiv : 0 ≤ K ^ ε / K := div_nonneg hKε.le hK0.le
    calc K ^ ε / K * ((4 * (K ^ ε) ^ 2 + 1) * (K ^ (1 + lam) + 1))
        ≤ K ^ ε / K * (10 * ((K ^ ε) ^ 2 * K ^ (1 + lam))) := mul_le_mul_of_nonneg_left hA hdiv
      _ = 10 * (K ^ ε / K * ((K ^ ε) ^ 2 * K ^ (1 + lam))) := by ring
      _ = 10 * K ^ (lam + 3 * ε) := by rw [hE]
      _ ≤ 10 * K ^ (lam + (3 + lam) * ε) := mul_le_mul_of_nonneg_left hmono (by norm_num)
  have hpow : (2 * K ^ (1 + ε)) ^ (1 + lam) = 2 ^ (1 + lam) * K ^ ((1 + ε) * (1 + lam)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hK0.le _), ← Real.rpow_mul hK0.le]
  have hT2 : K ^ ε / K * (2 * (2 * K ^ (1 + ε)) ^ (1 + lam) * (1 + Real.log M)) ≤
      2 ^ (2 + lam) * (1 + Real.log 4 + γ / ε) * K ^ (lam + (3 + lam) * ε) := by
    rw [hpow]
    have hpos : 0 ≤ K ^ ε / K * (2 * (2 ^ (1 + lam) * K ^ ((1 + ε) * (1 + lam)))) := by
      have : 0 ≤ K ^ ε / K := div_nonneg hKε.le hK0.le
      have : 0 ≤ K ^ ((1 + ε) * (1 + lam)) := Real.rpow_nonneg hK0.le _
      positivity
    have h22 : (2 : ℝ) ^ (2 + lam) = 2 * 2 ^ (1 + lam) := by
      rw [show (2 + lam) = 1 + (1 + lam) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
    have hK' : K ^ (ε - 1) * K ^ ((1 + ε) * (1 + lam)) * K ^ ε =
        K ^ (lam + (3 + lam) * ε) := by
      rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
      congr 1
      ring
    calc K ^ ε / K * (2 * (2 ^ (1 + lam) * K ^ ((1 + ε) * (1 + lam))) * (1 + Real.log M))
        = K ^ ε / K * (2 * (2 ^ (1 + lam) * K ^ ((1 + ε) * (1 + lam)))) * (1 + Real.log M) := by
          ring
      _ ≤ K ^ ε / K * (2 * (2 ^ (1 + lam) * K ^ ((1 + ε) * (1 + lam)))) *
            ((1 + Real.log 4 + γ / ε) * K ^ ε) := mul_le_mul_of_nonneg_left hlogbd hpos
      _ = 2 ^ (2 + lam) * (1 + Real.log 4 + γ / ε) * K ^ (lam + (3 + lam) * ε) := by
          rw [← hK', ← Real.rpow_sub_one hK0.ne' ε, h22]
          ring
  have hT3 : K ^ ε / K * (2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * K ^ (1 + ε)) ≤
      2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * K ^ (lam + (3 + lam) * ε) := by
    have h1 : K ^ ε / K * K ^ (1 + ε) = K ^ (2 * ε) := by
      rw [← Real.rpow_sub_one hK0.ne' ε, ← Real.rpow_add hK0]
      congr 1
      ring
    have hC0 : 0 ≤ 2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) := by
      have : 0 ≤ 2 ^ (3 - s) / ((3 - s) - 1) := div_nonneg (Real.rpow_nonneg (by norm_num) _)
        (by linarith)
      linarith
    have hmono : K ^ (2 * ε) ≤ K ^ (lam + (3 + lam) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hK1 (by nlinarith)
    calc K ^ ε / K * (2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * K ^ (1 + ε))
        = 2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * (K ^ ε / K * K ^ (1 + ε)) := by ring
      _ = 2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * K ^ (2 * ε) := by rw [h1]
      _ ≤ 2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * K ^ (lam + (3 + lam) * ε) :=
          mul_le_mul_of_nonneg_left hmono hC0
  have hgc : goodConst s γ lam ε * K ^ (lam + (3 + lam) * ε) =
      10 * K ^ (lam + (3 + lam) * ε) + 2 ^ (2 + lam) * (1 + Real.log 4 + γ / ε) *
        K ^ (lam + (3 + lam) * ε) + 2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) *
        K ^ (lam + (3 + lam) * ε) := by
    unfold goodConst
    ring
  rw [mul_add, mul_add, hgc]
  linarith [hT1, hT2, hT3]

/-- **Deterministic translation bound on the good event.** Let `0 < ε ≤ 1` with
`ε ≤ γ(1 - s/2)`, and let `N ℓ ≥ 1`. Let `f` be `C¹` with period `1/ℓ`, satisfying the derivative
majorant on the half period. For a configuration `X` on the good event and a shift
`0 ≤ D ≤ (N ℓ)^ε`, the translation error at the anchored vector `rotAnchorVec N X` satisfies
`|Δ_D| ≤ goodConst s γ λ ε · (N ℓ)^{λ + (3 + λ) ε}`. -/
theorem translationError_good_le {s γ lam ε : ℝ} (hs : 0 < s) (hs1 : s < 1) (hlam : 0 ≤ lam)
    (hγ : 1 < γ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεγ : ε ≤ γ * (1 - s / 2)) (N : ℕ+) (ℓ : ℝ)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK1 : 1 ≤ ((N : ℕ) : ℝ) * ℓ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f (1 / ℓ))
    (hder : ∀ u ∈ Set.Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ derivMajorant (((N : ℕ) : ℝ) * ℓ) lam s |u|)
    {X : Configuration N} (hX : X ∈ goodEvent N s (((N : ℕ) : ℝ) * ℓ) γ ε)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε) :
    |translationError N ℓ γ f D (rotAnchorVec N X)| ≤
      goodConst s γ lam ε * (((N : ℕ) : ℝ) * ℓ) ^ (lam + (3 + lam) * ε) := by
  set K : ℝ := ((N : ℕ) : ℝ) * ℓ with hK_def
  have hK0 : 0 < K := by linarith
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := hNpos.ne'
  have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK0 ε
  have hKε1 : 1 ≤ K ^ ε := Real.one_le_rpow hK1 hε.le
  have hKεK : K ^ ε ≤ K := by
    calc K ^ ε ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1 hε1
      _ = K := Real.rpow_one K
  have hDL : D / K ≤ 1 / ℓ := by
    have h1 : D / K ≤ 1 := (div_le_one hK0).2 (hD.trans hKεK)
    have h2 : 1 ≤ 1 / ℓ := by rw [le_div_iff₀ hℓ]; linarith
    linarith
  have hs3 : s < 3 := by linarith
  have hterm := abs_translationError_le_sum (γ := γ) N hℓ hK0 hs3 hlam hf hper hder hD0 hDL
    (rotAnchorVec N X)
  -- The microscopic distance `a i = N dist(1, y_i)` of each window label.
  obtain ⟨a, ha_def⟩ : ∃ a : Fin (N : ℕ) → ℝ,
      a = fun i => ((N : ℕ) : ℝ) * circDist 1 (rotAnchorVec N X i) := ⟨_, rfl⟩
  have ha : ∀ i, a i = ((N : ℕ) : ℝ) * circDist 1 (rotAnchorVec N X i) := fun i => by
    rw [ha_def]
  have hconv : ∀ i : Fin (N : ℕ), circDist 1 (rotAnchorVec N X i) / ℓ - D / K = (a i - D) / K := by
    intro i
    rw [ha i, sub_div, hK_def, mul_div_mul_left _ _ hNne]
  obtain ⟨I, hI_def⟩ : ∃ I : Finset (Fin (N : ℕ)), I = window N K γ := ⟨_, rfl⟩
  have hsum_eq : ∑ i ∈ window N K γ,
      derivMajorant K lam s (max (circDist 1 (rotAnchorVec N X i) / ℓ - D / K) 0) =
      ∑ i ∈ window N K γ, derivMajorant K lam s (max ((a i - D) / K) 0) :=
    Finset.sum_congr rfl fun i _ => by rw [hconv i]
  have hnn : ∀ t : ℝ, 0 ≤ derivMajorant K lam s t := fun t => by
    unfold derivMajorant
    have h1 : 0 ≤ 1 / (max t K⁻¹) ^ (1 + lam) :=
      div_nonneg zero_le_one (Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.2 hK0.le)) _)
    have h2 : 0 ≤ 1 / (max t 2) ^ (3 - s) :=
      div_nonneg zero_le_one (Real.rpow_nonneg (le_max_of_le_right (by norm_num)) _)
    linarith
  -- The near and far labels: `a i < 2 K^ε` or not.
  have hsplit := Finset.sum_filter_add_sum_filter_not (window N K γ) (fun i => a i < 2 * K ^ ε)
    (fun i => derivMajorant K lam s (max ((a i - D) / K) 0))
  have hdle : ∀ i ∈ window N K γ, (labelDistToOne N i : ℝ) ≤ 4 * K ^ γ :=
    fun i hi => labelDist_le_of_mem_window hK1 hi
  -- Near labels: few, and each term is at most `K^{1+λ} + 1`.
  set T : ℕ := ⌊2 * (K ^ ε) ^ 2⌋₊ with hT_def
  have hnear_card : ((window N K γ).filter (fun i => a i < 2 * K ^ ε)).card ≤
      4 * (K ^ ε) ^ 2 + 1 := by
    have hsub : (window N K γ).filter (fun i => a i < 2 * K ^ ε) ⊆
        univ.filter (fun i => labelDistToOne N i ≤ T) := by
      intro i hi
      rw [mem_filter] at hi
      obtain ⟨hiI, hia⟩ := hi
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hlow := (good_label_bounds hs hs1 hK1 (by linarith) hε.le hεγ hX hiI).1
      rw [← ha i] at hlow
      have h1 : K ^ (-ε) * (labelDistToOne N i : ℝ) * K ^ ε = labelDistToOne N i := by
        rw [Real.rpow_neg hK0.le, inv_mul_eq_div, div_mul_cancel₀ _ hKε.ne']
      have h3 : K ^ (-ε) * (labelDistToOne N i : ℝ) * K ^ ε ≤ a i * K ^ ε :=
        mul_le_mul_of_nonneg_right hlow hKε.le
      have h4 : a i * K ^ ε < 2 * K ^ ε * K ^ ε := mul_lt_mul_of_pos_right hia hKε
      have hd2 : (labelDistToOne N i : ℝ) ≤ 2 * (K ^ ε) ^ 2 := by
        rw [sq]
        linarith
      exact Nat.le_floor hd2
    have hcard := Finset.card_le_card hsub
    have hcard2 := card_labelDist_le N T
    have hTR : (T : ℝ) ≤ 2 * (K ^ ε) ^ 2 := Nat.floor_le (by positivity)
    have hcardR : (((window N K γ).filter (fun i => a i < 2 * K ^ ε)).card : ℝ) ≤ 2 * T + 1 := by
      have : ((window N K γ).filter (fun i => a i < 2 * K ^ ε)).card ≤ 2 * T + 1 :=
        hcard.trans hcard2
      exact_mod_cast this
    linarith
  have hnear : ∑ i ∈ (window N K γ).filter (fun i => a i < 2 * K ^ ε),
      derivMajorant K lam s (max ((a i - D) / K) 0) ≤
      (4 * (K ^ ε) ^ 2 + 1) * (K ^ (1 + lam) + 1) := by
    have hbd : ∀ i ∈ (window N K γ).filter (fun i => a i < 2 * K ^ ε),
        derivMajorant K lam s (max ((a i - D) / K) 0) ≤ K ^ (1 + lam) + 1 :=
      fun i _ => derivMajorant_le_near hK0 hlam hs1 (le_max_right _ _)
    calc ∑ i ∈ (window N K γ).filter (fun i => a i < 2 * K ^ ε),
          derivMajorant K lam s (max ((a i - D) / K) 0)
        ≤ ((window N K γ).filter (fun i => a i < 2 * K ^ ε)).card • (K ^ (1 + lam) + 1) :=
          Finset.sum_le_card_nsmul _ _ _ hbd
      _ = (((window N K γ).filter (fun i => a i < 2 * K ^ ε)).card : ℝ) * (K ^ (1 + lam) + 1) := by
          rw [nsmul_eq_mul]
      _ ≤ (4 * (K ^ ε) ^ 2 + 1) * (K ^ (1 + lam) + 1) :=
          mul_le_mul_of_nonneg_right hnear_card (by positivity)
  -- Far labels: `a i ≥ 2 K^ε`, so the distance `d_i ≥ 1` and the argument is at least `a_i/(2K)`.
  set M : ℕ := ⌊4 * K ^ γ⌋₊ with hM_def
  have hFar : ∀ i ∈ (window N K γ).filter (fun i => ¬ a i < 2 * K ^ ε),
      derivMajorant K lam s (max ((a i - D) / K) 0) ≤
        (2 * K ^ (1 + ε) / (labelDistToOne N i : ℝ)) ^ (1 + lam) +
          min (2 * K ^ (1 + ε) / (labelDistToOne N i : ℝ)) (1 / 2) ^ (3 - s) := by
    intro i hi
    rw [mem_filter] at hi
    obtain ⟨hiI, hia⟩ := hi
    have hia' : 2 * K ^ ε ≤ a i := not_lt.mp hia
    have hbd := good_label_bounds hs hs1 hK1 (by linarith) hε.le hεγ hX hiI
    rw [← ha i] at hbd
    obtain ⟨hlow, hup⟩ := hbd
    have hd1 : (1 : ℝ) ≤ (labelDistToOne N i : ℝ) := by
      have hpos : 0 < labelDistToOne N i := by
        rcases Nat.eq_zero_or_pos (labelDistToOne N i) with h0 | h0
        · rw [h0, Nat.cast_zero, mul_zero] at hup
          linarith
        · exact h0
      exact_mod_cast hpos
    have ha0 : 0 < a i := by linarith
    have hDa : D ≤ a i / 2 := by linarith
    have ht : a i / (2 * K) ≤ max ((a i - D) / K) 0 := by
      refine le_trans ?_ (le_max_left _ _)
      rw [show a i / (2 * K) = (a i / 2) / K by rw [div_div]]
      exact (div_le_div_iff_of_pos_right hK0).2 (by linarith)
    exact derivMajorant_far_le hK0 hlam hs1 hd1 ha0 hlow ht
  have hKγ1 : 1 ≤ K ^ γ := Real.one_le_rpow hK1 (by linarith)
  have hM1' : (1 : ℝ) ≤ M := by
    have h1 : 1 ≤ M := Nat.le_floor (by norm_num; linarith)
    exact_mod_cast h1
  -- Far sum: two power sums over the distances in `1 ≤ d ≤ M`.
  have hFarMem : ∀ i ∈ (window N K γ).filter (fun i => ¬ a i < 2 * K ^ ε),
      labelDistToOne N i ∈ Finset.Icc 1 M := by
    intro i hi
    rw [mem_filter] at hi
    obtain ⟨hiI, hia⟩ := hi
    have hia' : 2 * K ^ ε ≤ a i := not_lt.mp hia
    have hbd := good_label_bounds hs hs1 hK1 (by linarith) hε.le hεγ hX hiI
    rw [← ha i] at hbd
    obtain ⟨_, hup⟩ := hbd
    have hpos : 0 < labelDistToOne N i := by
      rcases Nat.eq_zero_or_pos (labelDistToOne N i) with h0 | h0
      · rw [h0, Nat.cast_zero, mul_zero] at hup
        linarith
      · exact h0
    refine Finset.mem_Icc.2 ⟨hpos, Nat.le_floor (hdle i hiI)⟩
  have hFA_nn : ∀ d : ℕ, 0 ≤ (2 * K ^ (1 + ε) / (d : ℝ)) ^ (1 + lam) := fun d =>
    Real.rpow_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) _
  have hFC_nn : ∀ d : ℕ, 0 ≤ min (2 * K ^ (1 + ε) / (d : ℝ)) (1 / 2) ^ (3 - s) := fun d =>
    Real.rpow_nonneg (le_min (div_nonneg (by positivity) (Nat.cast_nonneg _)) (by norm_num)) _
  have hfarA := sum_labelDist_le_two_mul ((window N K γ).filter (fun i => ¬ a i < 2 * K ^ ε))
    (F := fun d : ℕ => (2 * K ^ (1 + ε) / (d : ℝ)) ^ (1 + lam)) hFA_nn hFarMem
  have hfarC := sum_labelDist_le_two_mul ((window N K γ).filter (fun i => ¬ a i < 2 * K ^ ε))
    (F := fun d : ℕ => min (2 * K ^ (1 + ε) / (d : ℝ)) (1 / 2) ^ (3 - s)) hFC_nn hFarMem
  have hA1 : 1 ≤ K ^ (1 + ε) := Real.one_le_rpow hK1 (by linarith)
  have hsA := sum_Icc_rpow_div_le (X := 2 * K ^ (1 + ε)) (by positivity) hlam M
  have hsC := sum_Icc_min_rpow_le (A := K ^ (1 + ε)) (p := 3 - s) hA1 (by linarith) M
  have hfar : ∑ i ∈ (window N K γ).filter (fun i => ¬ a i < 2 * K ^ ε),
      derivMajorant K lam s (max ((a i - D) / K) 0) ≤
      2 * ((2 * K ^ (1 + ε)) ^ (1 + lam) * (1 + Real.log M)) +
        2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * K ^ (1 + ε) := by
    have hpt : ∑ i ∈ (window N K γ).filter (fun i => ¬ a i < 2 * K ^ ε),
        derivMajorant K lam s (max ((a i - D) / K) 0) ≤
        ∑ i ∈ (window N K γ).filter (fun i => ¬ a i < 2 * K ^ ε),
          ((fun d : ℕ => (2 * K ^ (1 + ε) / (d : ℝ)) ^ (1 + lam)) (labelDistToOne N i) +
            (fun d : ℕ => min (2 * K ^ (1 + ε) / (d : ℝ)) (1 / 2) ^ (3 - s)) (labelDistToOne N i)) :=
      Finset.sum_le_sum fun i hi => hFar i hi
    rw [Finset.sum_add_distrib] at hpt
    have hsA2 : (2 * K ^ (1 + ε)) ^ (1 + lam) * (1 + Real.log M) ≥ 0 := by
      have : 0 ≤ 1 + Real.log M := by
        have : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1'
        linarith
      positivity
    nlinarith [hpt, hfarA, hfarC, hsA, hsC]
  have hSigma : ∑ i ∈ window N K γ, derivMajorant K lam s (max ((a i - D) / K) 0) ≤
      (4 * (K ^ ε) ^ 2 + 1) * (K ^ (1 + lam) + 1) +
      2 * (2 * K ^ (1 + ε)) ^ (1 + lam) * (1 + Real.log M) +
      2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * K ^ (1 + ε) := by
    rw [← hsplit]
    have h2 : 2 * (2 * K ^ (1 + ε)) ^ (1 + lam) * (1 + Real.log M) =
        2 * ((2 * K ^ (1 + ε)) ^ (1 + lam) * (1 + Real.log M)) := by ring
    rw [h2]
    linarith [hnear, hfar]
  have hS0 : 0 ≤ ∑ i ∈ window N K γ, derivMajorant K lam s (max ((a i - D) / K) 0) :=
    Finset.sum_nonneg fun i _ => hnn _
  have hDK : D / K ≤ K ^ ε / K := div_le_div_of_nonneg_right hD hK0.le
  have hfinal : |translationError N ℓ γ f D (rotAnchorVec N X)| ≤
      K ^ ε / K * ((4 * (K ^ ε) ^ 2 + 1) * (K ^ (1 + lam) + 1) +
        2 * (2 * K ^ (1 + ε)) ^ (1 + lam) * (1 + Real.log M) +
        2 * (2 + 2 ^ (3 - s) / ((3 - s) - 1)) * K ^ (1 + ε)) := by
    refine hterm.trans ?_
    rw [← Finset.mul_sum, hsum_eq]
    have hmul1 : D / K * ∑ i ∈ window N K γ, derivMajorant K lam s (max ((a i - D) / K) 0) ≤
        K ^ ε / K * ∑ i ∈ window N K γ, derivMajorant K lam s (max ((a i - D) / K) 0) :=
      mul_le_mul_of_nonneg_right hDK hS0
    refine hmul1.trans ?_
    exact mul_le_mul_of_nonneg_left hSigma (div_nonneg hKε.le hK0.le)
  exact hfinal.trans (translation_power_bound M hK1 hs1 hlam hγ hε (Nat.floor_le (by positivity)) hM1')

end Riesz1
