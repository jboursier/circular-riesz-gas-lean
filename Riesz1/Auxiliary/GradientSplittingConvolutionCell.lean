/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingConvolutionLattice

/-!
# Cell variation of the microscopic weights

The convolution part of Lemma 5.7, the cell comparisons used in
its particle-level proof. A particle at a microscopic position `z` lies in the unit cell whose
integer left endpoint is `q`, so `|z - q| < 1`. The weights `W_1, W_2` change by a bounded factor
when the position moves by less than one microscopic unit.

Notation: `N ∈ ℕ+` is the number of particles, `ℓ > 0` the scale, `K = Nℓ`. The microscopic weight
`gradW2 s a N ℓ z = w_2(z/K)` lives on `N𝕋`, as the paper's `W_2(z) = w_2(z/K)`. Likewise
`gradW1 s a N ℓ z = w_1(z/K)`. Both are periodic with period `N` (`gradW2_add_mul`,
`gradW1_add_mul`).
-/

@[expose] public section

namespace Riesz1

noncomputable section

/-! ## Elementary inequalities for powers -/

/-- If `0 < x`, `0 < y`, `y ≤ 2x` and `e ≤ 0`, then `x^e ≤ 2^(-e) y^e`. -/
lemma rpow_le_two_pow_mul_rpow {x y e : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : y ≤ 2 * x)
    (he : e ≤ 0) : x ^ e ≤ (2 : ℝ) ^ (-e) * y ^ e := by
  have h1 : (2 * x) ^ e ≤ y ^ e := Real.rpow_le_rpow_of_nonpos hy hxy he
  have h2 : (2 * x) ^ e = (2 : ℝ) ^ e * x ^ e := Real.mul_rpow (by norm_num) hx.le
  have h3 : (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  have h4 : 0 ≤ (2 : ℝ) ^ (-e) := by positivity
  calc x ^ e = (2 : ℝ) ^ (-e) * ((2 : ℝ) ^ e * x ^ e) := by
        rw [← mul_assoc, h3, one_mul]
    _ = (2 : ℝ) ^ (-e) * (2 * x) ^ e := by rw [h2]
    _ ≤ (2 : ℝ) ^ (-e) * y ^ e := mul_le_mul_of_nonneg_left h1 h4

/-- The power `(1/2)^e` equals `2^(-e)`. -/
lemma half_rpow_eq (e : ℝ) : ((1 : ℝ) / 2) ^ e = (2 : ℝ) ^ (-e) := by
  rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]

/-- Moving the base point by at most one unit changes `(1 + x)^(-p)` by at most `2^p`:
`(1 + x)^(-p) ≤ 2^p (1 + y)^(-p)` when `x, y ≥ 0`, `|x - y| ≤ 1` and `p ≥ 0`. -/
lemma rpow_one_add_neg_le_two_pow {p x y : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : |x - y| ≤ 1) : (1 + x) ^ (-p) ≤ (2 : ℝ) ^ p * (1 + y) ^ (-p) := by
  have hab := abs_le.mp h
  have h1 : (1 + y) ≤ 2 * (1 + x) := by linarith [hab.1]
  have h2 := rpow_le_two_pow_mul_rpow (x := 1 + x) (y := 1 + y) (e := -p) (by linarith)
    (by linarith) h1 (by linarith)
  rw [neg_neg] at h2
  exact h2

/-! ## Circular distance facts -/

/-- The circular distance is at most the absolute value of the argument. -/
lemma circDist_le_abs_self {L : ℝ} (hL : 0 < L) (x : ℝ) : circDist L x ≤ |x| := by
  have h := circDist_le_abs_sub_int hL x 0
  simpa using h

/-- The circular distances of two points differ by at most the circular distance of their
difference. -/
lemma abs_circDist_sub_circDist_le {L a b : ℝ} (hL : 0 < L) :
    |circDist L a - circDist L b| ≤ circDist L (a - b) := by
  rw [abs_le]
  constructor
  · have h := circDist_triangle hL a (b - a)
    rw [show a + (b - a) = b by ring] at h
    have h' := circDist_neg hL (a - b)
    rw [show -(a - b) = b - a by ring] at h'
    linarith
  · have h := circDist_triangle hL (a - b) b
    rw [show a - b + b = a by ring] at h
    linarith

/-- Two points at distance at most one have circular distances differing by at most one. -/
lemma circDist_le_add_one_of_abs_sub_le {L a b : ℝ} (hL : 0 < L) (h : |a - b| ≤ 1) :
    circDist L a ≤ circDist L b + 1 := by
  have h1 := abs_circDist_sub_circDist_le (a := a) (b := b) hL
  have h2 := circDist_le_abs_self hL (a - b)
  linarith [le_abs_self (circDist L a - circDist L b)]

/-! ## Scalar cell comparisons for `w_1` and `w_2`

The weights are of the form `Ψ(t)`, where `t` is a circular distance and `Ψ` is a piecewise
power. The comparison below uses only `t_v ≤ t_z + c` with `c ≤ 1`. -/

/-- The scalar cell comparison for `w_2`: if `t_v ≤ t_z + c`, then the value of `Ψ_2` at `t_z` is at
most `2^(4+a)` times its value at `t_v`. -/
lemma gradPsiTwo_cell_le {s a c tz tv : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (h : tv ≤ tz + c) :
    (if tz < 1 then max tz c ^ (-(1 + a)) else tz ^ (s - 3))
      ≤ 2 ^ (4 + a) * (if tv < 1 then max tv c ^ (-(1 + a)) else tv ^ (s - 3)) := by
  have hmz : 0 < max tz c := lt_max_of_lt_right hc0
  have hmv : 0 < max tv c := lt_max_of_lt_right hc0
  have h2pos : (0 : ℝ) < 2 ^ (4 + a) := by positivity
  have h1le : (1 : ℝ) ≤ 2 ^ (4 + a) := Real.one_le_rpow (by norm_num) (by linarith)
  by_cases hz : tz < 1 <;> by_cases hv : tv < 1
  · simp only [hz, hv, ↓reduceIte]
    have hcap : max tv c ≤ 2 * max tz c := by
      apply max_le
      · linarith [le_max_left tz c, le_max_right tz c]
      · linarith [le_max_right tz c]
    have h1 := rpow_le_two_pow_mul_rpow hmz hmv hcap (by linarith : -(1 + a) ≤ 0)
    rw [neg_neg] at h1
    have h2 : (2 : ℝ) ^ (1 + a) ≤ 2 ^ (4 + a) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : 0 ≤ max tv c ^ (-(1 + a)) := Real.rpow_nonneg hmv.le _
    calc max tz c ^ (-(1 + a)) ≤ 2 ^ (1 + a) * max tv c ^ (-(1 + a)) := h1
      _ ≤ 2 ^ (4 + a) * max tv c ^ (-(1 + a)) := mul_le_mul_of_nonneg_right h2 h3
  · simp only [hz, hv, ↓reduceIte]
    have hv1 : 1 ≤ tv := not_lt.mp hv
    have htv2 : tv ≤ 2 := by linarith
    have hx : (1 / 2 : ℝ) ≤ max tz c := by
      rcases le_total c (1 / 2) with hc | hc
      · exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right hc
    have h1 : max tz c ^ (-(1 + a)) ≤ (1 / 2 : ℝ) ^ (-(1 + a)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)
    rw [half_rpow_eq, neg_neg] at h1
    have h2 : (2 : ℝ) ^ (s - 3) ≤ tv ^ (s - 3) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) htv2 (by linarith)
    have h3 : (2 : ℝ) ^ (1 + a) ≤ 2 ^ (4 + a) * 2 ^ (s - 3) := by
      rw [← Real.rpow_add (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc max tz c ^ (-(1 + a)) ≤ 2 ^ (1 + a) := h1
      _ ≤ 2 ^ (4 + a) * 2 ^ (s - 3) := h3
      _ ≤ 2 ^ (4 + a) * tv ^ (s - 3) := mul_le_mul_of_nonneg_left h2 h2pos.le
  · simp only [hz, hv, ↓reduceIte]
    have hz1 : 1 ≤ tz := not_lt.mp hz
    have h1 : tz ^ (s - 3) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith)
    have h2 : 1 ≤ max tv c ^ (-(1 + a)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hmv (max_le hv.le hc1) (by linarith)
    calc tz ^ (s - 3) ≤ 1 := h1
      _ ≤ max tv c ^ (-(1 + a)) := h2
      _ ≤ 2 ^ (4 + a) * max tv c ^ (-(1 + a)) := le_mul_of_one_le_left (by linarith) h1le
  · simp only [hz, hv, ↓reduceIte]
    have hz1 : 1 ≤ tz := not_lt.mp hz
    have hv1 : 1 ≤ tv := not_lt.mp hv
    have htv2 : tv ≤ 2 * tz := by linarith
    have hpz : 0 < tz := by linarith
    have hpv : 0 < tv := by linarith
    have h1 := rpow_le_two_pow_mul_rpow hpz hpv htv2 (by linarith : s - 3 ≤ 0)
    have h2 : (2 : ℝ) ^ (-(s - 3)) ≤ 2 ^ (4 + a) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : 0 ≤ tv ^ (s - 3) := Real.rpow_nonneg hpv.le _
    calc tz ^ (s - 3) ≤ 2 ^ (-(s - 3)) * tv ^ (s - 3) := h1
      _ ≤ 2 ^ (4 + a) * tv ^ (s - 3) := mul_le_mul_of_nonneg_right h2 h3

/-- The scalar cell comparison for `w_1`: if `t_v ≤ t_z + c`, then the value of `Ψ_1` at `t_z` is
at most `2^(2+a)` times its value at `t_v`. -/
lemma gradPsiOne_cell_le {s a c tz tv : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (h : tv ≤ tz + c) :
    (if tz < 1 then max tz c ^ (-a) else tz ^ (s - 2))
      ≤ 2 ^ (2 + a) * (if tv < 1 then max tv c ^ (-a) else tv ^ (s - 2)) := by
  have hmz : 0 < max tz c := lt_max_of_lt_right hc0
  have hmv : 0 < max tv c := lt_max_of_lt_right hc0
  have h2pos : (0 : ℝ) < 2 ^ (2 + a) := by positivity
  have h1le : (1 : ℝ) ≤ 2 ^ (2 + a) := Real.one_le_rpow (by norm_num) (by linarith)
  by_cases hz : tz < 1 <;> by_cases hv : tv < 1
  · simp only [hz, hv, ↓reduceIte]
    have hcap : max tv c ≤ 2 * max tz c := by
      apply max_le
      · linarith [le_max_left tz c, le_max_right tz c]
      · linarith [le_max_right tz c]
    have h1 := rpow_le_two_pow_mul_rpow hmz hmv hcap (by linarith : -a ≤ 0)
    rw [neg_neg] at h1
    have h2 : (2 : ℝ) ^ a ≤ 2 ^ (2 + a) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : 0 ≤ max tv c ^ (-a) := Real.rpow_nonneg hmv.le _
    calc max tz c ^ (-a) ≤ 2 ^ a * max tv c ^ (-a) := h1
      _ ≤ 2 ^ (2 + a) * max tv c ^ (-a) := mul_le_mul_of_nonneg_right h2 h3
  · simp only [hz, hv, ↓reduceIte]
    have hv1 : 1 ≤ tv := not_lt.mp hv
    have htv2 : tv ≤ 2 := by linarith
    have hx : (1 / 2 : ℝ) ≤ max tz c := by
      rcases le_total c (1 / 2) with hc | hc
      · exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right hc
    have h1 : max tz c ^ (-a) ≤ (1 / 2 : ℝ) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)
    rw [half_rpow_eq, neg_neg] at h1
    have h2 : (2 : ℝ) ^ (s - 2) ≤ tv ^ (s - 2) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) htv2 (by linarith)
    have h3 : (2 : ℝ) ^ a ≤ 2 ^ (2 + a) * 2 ^ (s - 2) := by
      rw [← Real.rpow_add (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc max tz c ^ (-a) ≤ 2 ^ a := h1
      _ ≤ 2 ^ (2 + a) * 2 ^ (s - 2) := h3
      _ ≤ 2 ^ (2 + a) * tv ^ (s - 2) := mul_le_mul_of_nonneg_left h2 h2pos.le
  · simp only [hz, hv, ↓reduceIte]
    have hz1 : 1 ≤ tz := not_lt.mp hz
    have h1 : tz ^ (s - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith)
    have h2 : 1 ≤ max tv c ^ (-a) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hmv (max_le hv.le hc1) (by linarith)
    calc tz ^ (s - 2) ≤ 1 := h1
      _ ≤ max tv c ^ (-a) := h2
      _ ≤ 2 ^ (2 + a) * max tv c ^ (-a) := le_mul_of_one_le_left (by linarith) h1le
  · simp only [hz, hv, ↓reduceIte]
    have hz1 : 1 ≤ tz := not_lt.mp hz
    have hv1 : 1 ≤ tv := not_lt.mp hv
    have htv2 : tv ≤ 2 * tz := by linarith
    have hpz : 0 < tz := by linarith
    have hpv : 0 < tv := by linarith
    have h1 := rpow_le_two_pow_mul_rpow hpz hpv htv2 (by linarith : s - 2 ≤ 0)
    have h2 : (2 : ℝ) ^ (-(s - 2)) ≤ 2 ^ (2 + a) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : 0 ≤ tv ^ (s - 2) := Real.rpow_nonneg hpv.le _
    calc tz ^ (s - 2) ≤ 2 ^ (-(s - 2)) * tv ^ (s - 2) := h1
      _ ≤ 2 ^ (2 + a) * tv ^ (s - 2) := mul_le_mul_of_nonneg_right h2 h3

/-! ## Cell comparisons for the weights on a circle -/

/-- Cell comparison for `w_2` on the circle `(N/K)𝕋`: if `circDist N v ≤ circDist N z + 1`, then
`w_2(z/K) ≤ 2^(4+a) w_2(v/K)`. -/
lemma gradWeightTwo_cell_le {s a K N z v : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a)
    (hK : 1 ≤ K) (h : circDist N v ≤ circDist N z + 1) :
    gradWeightTwo s a K (N / K) (z / K) ≤ 2 ^ (4 + a) * gradWeightTwo s a K (N / K) (v / K) := by
  have hK0 : 0 < K := by linarith
  have hc1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  unfold gradWeightTwo
  rw [circDist_scale hK0, circDist_scale hK0]
  refine gradPsiTwo_cell_le hs0 hs1 ha (inv_pos.mpr hK0) hc1 ?_
  rw [show circDist N z / K + K⁻¹ = (circDist N z + 1) / K by field_simp]
  exact div_le_div_of_nonneg_right h hK0.le

/-- Cell comparison for `w_1` on the circle `(N/K)𝕋`, in squared form. -/
lemma gradWeightOne_cell_sq_le {s a K N z v : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a)
    (hK : 1 ≤ K) (h : circDist N v ≤ circDist N z + 1) :
    gradWeightOne s a K (N / K) (z / K) ^ 2
      ≤ (2 ^ (2 + a)) ^ 2 * gradWeightOne s a K (N / K) (v / K) ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hc1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hlin : gradWeightOne s a K (N / K) (z / K) ≤
      2 ^ (2 + a) * gradWeightOne s a K (N / K) (v / K) := by
    unfold gradWeightOne
    rw [circDist_scale hK0, circDist_scale hK0]
    refine gradPsiOne_cell_le hs0 hs1 ha (inv_pos.mpr hK0) hc1 ?_
    rw [show circDist N z / K + K⁻¹ = (circDist N z + 1) / K by field_simp]
    exact div_le_div_of_nonneg_right h hK0.le
  have h0 : 0 ≤ gradWeightOne s a K (N / K) (z / K) :=
    gradWeightOne_nonneg_unconditional _ _ _ _ _
  rw [← mul_pow]
  exact pow_le_pow_left₀ h0 hlin 2

/-! ## The microscopic weights

`gradW2 s a N ℓ z` is the paper's `W_2(z) = w_2(z/K)` on `N𝕋`, with `K = Nℓ`. `gradW1` is the
analogue for `w_1`. -/

/-- The microscopic weight `W_2(z) = w_2(z/K)` with `K = Nℓ` (convolution part of Lemma 5.7). -/
def gradW2 (s a : ℝ) (N : ℕ+) (ℓ z : ℝ) : ℝ :=
  gradWeightTwo s a (((N : ℕ) : ℝ) * ℓ) (((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) * ℓ))
    (z / (((N : ℕ) : ℝ) * ℓ))

/-- The microscopic weight `W_1(z) = w_1(z/K)` with `K = Nℓ` (convolution part of Lemma 5.7). -/
def gradW1 (s a : ℝ) (N : ℕ+) (ℓ z : ℝ) : ℝ :=
  gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) (((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) * ℓ))
    (z / (((N : ℕ) : ℝ) * ℓ))

/-- The microscopic `W_2` is periodic with period `N`. -/
lemma gradW2_add_mul (s a : ℝ) (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) (z : ℝ) (m : ℤ) :
    gradW2 s a N ℓ (z + m * ((N : ℕ) : ℝ)) = gradW2 s a N ℓ z := by
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := mul_pos hN hℓ
  unfold gradW2
  apply gradWeightTwo_congr
  rw [circDist_scale hK0, circDist_scale hK0, circDist_add_int_mul hN z m]

/-- The microscopic `W_1` is periodic with period `N`. -/
lemma gradW1_add_mul (s a : ℝ) (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) (z : ℝ) (m : ℤ) :
    gradW1 s a N ℓ (z + m * ((N : ℕ) : ℝ)) = gradW1 s a N ℓ z := by
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := mul_pos hN hℓ
  unfold gradW1
  apply gradWeightOne_congr
  rw [circDist_scale hK0, circDist_scale hK0, circDist_add_int_mul hN z m]

/-- Cell comparison for the microscopic `W_2`. -/
lemma gradW2_cell_le (s a : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) (N : ℕ+) {ℓ z v : ℝ}
    (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ)
    (h : circDist ((N : ℕ) : ℝ) v ≤ circDist ((N : ℕ) : ℝ) z + 1) :
    gradW2 s a N ℓ z ≤ 2 ^ (4 + a) * gradW2 s a N ℓ v := by
  unfold gradW2
  exact gradWeightTwo_cell_le hs0 hs1 ha hK h

/-- Cell comparison for the squared microscopic `W_1`. -/
lemma gradW1_cell_sq_le (s a : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) (N : ℕ+) {ℓ z v : ℝ}
    (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ)
    (h : circDist ((N : ℕ) : ℝ) v ≤ circDist ((N : ℕ) : ℝ) z + 1) :
    gradW1 s a N ℓ z ^ 2 ≤ (2 ^ (2 + a)) ^ 2 * gradW1 s a N ℓ v ^ 2 := by
  unfold gradW1
  exact gradWeightOne_cell_sq_le hs0 hs1 ha hK h

end

end Riesz1
