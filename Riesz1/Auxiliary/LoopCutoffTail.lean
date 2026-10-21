/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffEvent

/-!
# Tail estimates and reductions for the anchored cutoff

Support for the probability bound of the cutoff part of Lemma 5.8
(`LoopCutoffProbability.lean`). This file proves three kinds of elementary facts:

* a stretched-exponential tail `exp(-c K^θ) ≤ C K^{-b}` for `K ≥ 1`.
* reductions of the cyclic-lift differences `N (x_{i+k} - x_i) - k` to block lengths
  `blockLength X j m` with a forward block `m = |k|` and a base label `j`, and the reduction of
  `j` modulo `N`.
* the window bounds: every label of `I_{2γ}` and every pair `(i, i+k)` of `I_{2γ}` with `2|k| ≤ N`
  satisfies `|j| ≤ A` and `|k| ≤ A`, where `A = ⌊8 K^{2γ}⌋` and `K = Nℓ`.
-/

@[expose] public section

namespace Riesz1

noncomputable section

/-! ## Stretched-exponential tails -/

/-- For `c, θ > 0` and `b ≥ 0`, the bound `exp(-c K^θ) ≤ C K^{-b}` holds uniformly for `K ≥ 1`. -/
lemma exp_neg_rpow_le {c θ b : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → Real.exp (-(c * K ^ θ)) ≤ C * K ^ (-b) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b ≤ n * θ :=
    ⟨⌈b / θ⌉₊, by
      have h := Nat.le_ceil (b / θ)
      rwa [div_le_iff₀ hθ] at h⟩
  refine ⟨(n.factorial : ℝ) / c ^ n, by positivity, fun K hK => ?_⟩
  have hK0 : 0 < K := by linarith
  have hKθ : 0 < K ^ θ := Real.rpow_pos_of_pos hK0 θ
  have hy : 0 < c * K ^ θ := mul_pos hc hKθ
  have hpow_eq : (K ^ θ) ^ n = K ^ (θ * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
  have hyn : (c * K ^ θ) ^ n = c ^ n * K ^ (θ * n) := by
    rw [mul_pow, hpow_eq]
  have hKb : K ^ b ≤ K ^ (θ * n) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  have hpow : c ^ n * K ^ b ≤ (c * K ^ θ) ^ n := by
    rw [hyn]
    exact mul_le_mul_of_nonneg_left hKb (by positivity)
  have hexp : (c * K ^ θ) ^ n / n.factorial ≤ Real.exp (c * K ^ θ) :=
    Real.pow_div_factorial_le_exp (c * K ^ θ) hy.le n
  have hexp' : (c * K ^ θ) ^ n ≤ Real.exp (c * K ^ θ) * n.factorial :=
    (div_le_iff₀ (by positivity)).mp hexp
  have e : Real.exp (-(c * K ^ θ)) * (Real.exp (c * K ^ θ) * n.factorial) = n.factorial := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have key : Real.exp (-(c * K ^ θ)) * (c ^ n * K ^ b) ≤ n.factorial := by
    calc Real.exp (-(c * K ^ θ)) * (c ^ n * K ^ b)
        ≤ Real.exp (-(c * K ^ θ)) * (c * K ^ θ) ^ n :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ ≤ Real.exp (-(c * K ^ θ)) * (Real.exp (c * K ^ θ) * n.factorial) :=
          mul_le_mul_of_nonneg_left hexp' (Real.exp_pos _).le
      _ = n.factorial := e
  have hKb0 : 0 < K ^ b := Real.rpow_pos_of_pos hK0 b
  have hcn : 0 < c ^ n := pow_pos hc n
  rw [Real.rpow_neg hK0.le]
  calc Real.exp (-(c * K ^ θ))
      = Real.exp (-(c * K ^ θ)) * (c ^ n * K ^ b) / (c ^ n * K ^ b) := by
        field_simp
    _ ≤ (n.factorial : ℝ) / (c ^ n * K ^ b) :=
        div_le_div_of_nonneg_right key (by positivity)
    _ = (n.factorial : ℝ) / c ^ n * (K ^ b)⁻¹ := by ring

/-! ## Reductions of cyclic lifts -/

variable {N : ℕ+}

/-- Shifting a cyclic lift by a multiple of `N` adds the same integer to the lift. -/
lemma cyclicLift_add_N_mul (X : Configuration N) (j q : ℤ) :
    cyclicLift X (j + (N : ℤ) * q) = cyclicLift X j + q := by
  have h := gradLift_add_mul N X.val j q
  rwa [gradLift_val, gradLift_val] at h

/-- The difference of two lifts depends only on the labels modulo `N`:
`x_{j+m} - x_j = x_{(j mod N)+m} - x_{j mod N}`. -/
lemma cyclicLift_sub_eq_mod (X : Configuration N) (j m : ℤ) :
    cyclicLift X (j + m) - cyclicLift X j
      = cyclicLift X (j % (N : ℤ) + m) - cyclicLift X (j % (N : ℤ)) := by
  have hj : j % (N : ℤ) + (N : ℤ) * (j / (N : ℤ)) = j := by
    rw [Int.emod_def]
    ring
  have e1 := cyclicLift_add_N_mul X (j % (N : ℤ) + m) (j / (N : ℤ))
  have e2 := cyclicLift_add_N_mul X (j % (N : ℤ)) (j / (N : ℤ))
  rw [show j % (N : ℤ) + m + (N : ℤ) * (j / (N : ℤ)) = j + m by linarith] at e1
  rw [hj] at e2
  rw [e1, e2]
  ring

/-- A block length from a label, reduced modulo `N`. -/
lemma blockLength_eq_mod (X : Configuration N) (j : ℤ) (m : ℕ) :
    blockLength X j m
      = (N : ℝ) * (cyclicLift X (j % (N : ℤ) + m) - cyclicLift X (j % (N : ℤ))) := by
  unfold blockLength
  rw [cyclicLift_sub_eq_mod X j (m : ℤ)]

/-- The index of `Fin N` attached to a label `j`, namely the residue `j mod N`. -/
lemma gradIndex_val_cast (j : ℤ) :
    (((gradIndex N j : Fin (N : ℕ)) : ℕ) : ℤ) = j % (N : ℤ) := by
  have hN : (0 : ℤ) ≤ (N : ℤ) := by positivity
  unfold gradIndex
  simp only
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast N.ne_zero))

/-- The base label of the forward block that represents the pair `(i, i+k)`: `i` for `k ≥ 0`, and
`i + k` for `k < 0` (so that the block runs forward from the base to `i`). -/
def pairBase (i k : ℤ) : ℤ := if 0 ≤ k then i else i + k

/-- The absolute pair difference equals the absolute difference of a forward block length and its
length, with the base `pairBase i k` independent of the configuration. -/
lemma abs_pair_eq_block (X : Configuration N) (i k : ℤ) :
    |(N : ℝ) * (cyclicLift X (i + k) - cyclicLift X i) - (k : ℝ)|
      = |blockLength X (pairBase i k) k.natAbs - (k.natAbs : ℝ)| := by
  by_cases hk : 0 ≤ k
  · have hnat : ((k.natAbs : ℕ) : ℤ) = k := by omega
    have hcast : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      rw [← Int.cast_natCast, hnat]
    have hbase : pairBase i k = i := by simp [pairBase, hk]
    rw [hcast, hbase]
    unfold blockLength
    rw [show i + ((k.natAbs : ℕ) : ℤ) = i + k by rw [hnat]]
  · have hk' : k < 0 := not_le.mp hk
    have hnat : ((k.natAbs : ℕ) : ℤ) = -k := by omega
    have hcast : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      rw [← Int.cast_natCast, hnat]
      push_cast
      ring
    have hbase : pairBase i k = i + k := by simp [pairBase, not_le.mpr hk']
    rw [hcast, hbase]
    unfold blockLength
    rw [show i + k + ((k.natAbs : ℕ) : ℤ) = i by rw [hnat]; ring, ← abs_neg]
    congr 1
    ring

/-! ## Window bounds -/

/-- In a partial window, every label is bounded by `⌊M⌋` in absolute value. -/
lemma gradLabels_abs_le_floor {ℓ γ : ℝ} {j : ℤ} (hP : GradPartial N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) : |j| ≤ ⌊gradM N ℓ γ⌋ := by
  have hj' := hj
  unfold gradLabels at hj'
  simp only [hP, ↓reduceIte, Finset.mem_Icc] at hj'
  exact abs_le.mpr hj'

/-- In a full window, every label lies in `[0, N)`. -/
lemma gradLabels_full_bounds {ℓ γ : ℝ} {j : ℤ} (hP : ¬GradPartial N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) : 0 ≤ j ∧ j < (N : ℤ) := by
  have hj' := hj
  unfold gradLabels at hj'
  simp only [hP, ↓reduceIte, Finset.mem_Ico] at hj'
  exact hj'

/-- Outside a partial window, `N ≤ 8 M`. -/
lemma N_le_eight_mul_gradM {ℓ γ : ℝ} (hP : ¬GradPartial N ℓ γ) :
    (N : ℝ) ≤ 8 * gradM N ℓ γ := by
  unfold GradPartial at hP
  have h := not_lt.mp hP
  linarith

/-- The integer bound `A = ⌊8 K^{2γ}⌋`, with `K = Nℓ`, on the labels and pairs of `I_{2γ}`. -/
def loopBound (N : ℕ+) (ℓ γ : ℝ) : ℤ := ⌊8 * gradM N ℓ (2 * γ)⌋

/-- The scale `M = K^γ` is nonnegative for `ℓ > 0`. -/
lemma gradM_nonneg {ℓ γ : ℝ} (hℓ : 0 < ℓ) : 0 ≤ gradM N ℓ γ := by
  unfold gradM
  exact Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hℓ.le) _

/-- Every label of `I_{2γ}` satisfies `|j| ≤ A`. -/
lemma abs_le_loopBound_of_mem {ℓ γ : ℝ} (hℓ : 0 < ℓ) {j : ℤ}
    (hj : j ∈ gradLabels N ℓ (2 * γ)) : |j| ≤ loopBound N ℓ γ := by
  unfold loopBound
  have hM := gradM_nonneg (N := N) (γ := 2 * γ) hℓ
  by_cases hP : GradPartial N ℓ (2 * γ)
  · have h1 := gradLabels_abs_le_floor hP hj
    have h2 : ⌊gradM N ℓ (2 * γ)⌋ ≤ ⌊8 * gradM N ℓ (2 * γ)⌋ :=
      Int.floor_le_floor (by linarith)
    linarith
  · obtain ⟨h0, hN⟩ := gradLabels_full_bounds hP hj
    have hNR : (N : ℝ) ≤ 8 * gradM N ℓ (2 * γ) := N_le_eight_mul_gradM hP
    have hjR : (j : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [abs_of_nonneg h0]
    apply Int.le_floor.mpr
    linarith

/-- Every pair `(i, i+k)` of `I_{2γ}` with `2|k| ≤ N` has `|k| ≤ A`. -/
lemma abs_le_loopBound_of_window {ℓ γ : ℝ} (hℓ : 0 < ℓ) {i k : ℤ}
    (hi : i ∈ gradLabels N ℓ (2 * γ)) (hw : gradInWindow N ℓ (2 * γ) (i + k))
    (hk : 2 * |k| ≤ (N : ℤ)) : |k| ≤ loopBound N ℓ γ := by
  unfold loopBound
  have hM := gradM_nonneg (N := N) (γ := 2 * γ) hℓ
  by_cases hP : GradPartial N ℓ (2 * γ)
  · have hik : i + k ∈ gradLabels N ℓ (2 * γ) := hw hP
    have h1 := gradLabels_abs_le_floor hP hi
    have h2 := gradLabels_abs_le_floor hP hik
    have h3 : 2 * ⌊gradM N ℓ (2 * γ)⌋ ≤ ⌊8 * gradM N ℓ (2 * γ)⌋ := by
      apply Int.le_floor.mpr
      push_cast
      linarith [Int.floor_le (gradM N ℓ (2 * γ))]
    have h4 : |k| ≤ |i + k| + |i| := by
      have := abs_sub (i + k) i
      rwa [show i + k - i = k by ring] at this
    linarith
  · have hNR : (N : ℝ) ≤ 8 * gradM N ℓ (2 * γ) := N_le_eight_mul_gradM hP
    have hk' : (2 : ℝ) * ((|k| : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    apply Int.le_floor.mpr
    linarith

end

end Riesz1
