/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingZArc

/-!
# Averaged derivatives and the weight bound for `Z`

The differences part of Lemma 5.7, the bound
`|Z(x,y)| ≤ C C_0 (w_1(x/ℓ) + w_1(y/ℓ))`. Work in the variable `u = x/ℓ` on the circle `L𝕋` with
`L = ℓ^{-1}`. The average `gradZavg ψ p q = ∫_0^1 ψ'(p + θ(q - p)) dθ` is the paper's `Z`.

The proof splits the segment between `p` and `q` according to whether it contains a point of
`Lℤ`:

* No such point: the circular distance on the segment is at least the smaller endpoint distance,
  so `|ψ'| ≤ C_0 w_1` gives the bound directly.
* Such a point `nL` lies on the segment. Then both endpoint distances are at most the length `lam`
  of the segment, and there are two cases. If both endpoints are at distance at least `1`, the
  antipodal bound of `gradSplit_antipode_bound` applies. If one endpoint is within distance `1`,
  both one-sided integrals `G` from the origin are bounded.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- The average `∫_0^1 ψ'(p + θ(q-p)) dθ` of the derivative over the segment from `p` to `q`.
In the paper this is `Z`, written in the variable `u = x/ℓ`. -/
noncomputable def gradZavg (ψ : ℝ → ℝ) (p q : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, deriv ψ (p + θ * (q - p))

/-- The average is symmetric in its endpoints. -/
lemma gradZavg_symm (ψ : ℝ → ℝ) (p q : ℝ) : gradZavg ψ p q = gradZavg ψ q p := by
  unfold gradZavg
  have h := intervalIntegral.integral_comp_sub_left (fun θ => deriv ψ (q + θ * (p - q)))
    (1 : ℝ) (a := (0 : ℝ)) (b := 1)
  simp only [sub_zero, sub_self] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  congr 1
  ring

/-- For distinct endpoints the average is the difference quotient of `ψ`. -/
lemma gradZavg_eq_div {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {p q : ℝ} (hpq : p ≠ q) :
    gradZavg ψ p q = (ψ q - ψ p) / (q - p) := by
  unfold gradZavg
  have e : (fun θ : ℝ => deriv ψ (p + θ * (q - p))) = fun θ => deriv ψ ((q - p) * θ + p) := by
    funext θ
    congr 1
    ring
  rw [e, intervalIntegral.integral_comp_mul_add (fun t => deriv ψ t) (sub_ne_zero.mpr hpq.symm) p]
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hFTC : ∫ t in p..q, deriv ψ t = ψ q - ψ p :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hψ.differentiable (by simp) t).hasDerivAt)
      (hcont.intervalIntegrable _ _)
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
  rw [hFTC, smul_eq_mul, div_eq_inv_mul]

/-- Two points of a segment are at distance at most the length of the segment. -/
lemma abs_sub_le_of_mem_uIcc {p q x y : ℝ} (hx : x ∈ uIcc p q) (hy : y ∈ uIcc p q) :
    |x - y| ≤ |q - p| := by
  rcases le_total p q with hpq | hpq
  · rw [uIcc_of_le hpq] at hx hy
    rw [abs_of_nonneg (by linarith : 0 ≤ q - p), abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · rw [uIcc_of_ge hpq] at hx hy
    rw [abs_of_nonpos (by linarith : q - p ≤ 0), abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The weight `w_1` is nonnegative. -/
lemma gradWeightOne_nonneg {s a K L u : ℝ} (hK : 1 ≤ K) : 0 ≤ gradWeightOne s a K L u := by
  have hK0 : 0 < K⁻¹ := inv_pos.mpr (by linarith)
  unfold gradWeightOne
  split_ifs
  · exact Real.rpow_nonneg (le_trans hK0.le (le_max_right _ _)) _
  · exact Real.rpow_nonneg (abs_nonneg _) _

/-- The weight `w_2` is nonnegative. -/
lemma gradWeightTwo_nonneg {s a K L u : ℝ} (hK : 1 ≤ K) : 0 ≤ gradWeightTwo s a K L u := by
  have hK0 : 0 < K⁻¹ := inv_pos.mpr (by linarith)
  unfold gradWeightTwo
  split_ifs
  · exact Real.rpow_nonneg (le_trans hK0.le (le_max_right _ _)) _
  · exact Real.rpow_nonneg (abs_nonneg _) _

/-- The weight `w_1` on a segment with no point of `Lℤ` is at most its larger endpoint value. -/
lemma gradWeightOne_le_max_uIcc {s a K L p q t : ℝ} (hL : 0 < L) (hs1 : s < 1) (ha : 0 ≤ a)
    (hK : 1 ≤ K) (hno : ∀ n : ℤ, ¬(n * L ∈ uIcc p q)) (ht : t ∈ uIcc p q) :
    gradWeightOne s a K L t ≤ max (gradWeightOne s a K L p) (gradWeightOne s a K L q) := by
  rcases le_total p q with hpq | hpq
  · rw [uIcc_of_le hpq] at ht hno
    refine gradWeightOne_le_max_of_no_lattice hL hs1 ha hK (fun n hn => hno n ?_) ht
    exact Set.mem_Icc.mpr hn
  · rw [uIcc_of_ge hpq] at ht hno
    rw [max_comm]
    refine gradWeightOne_le_max_of_no_lattice hL hs1 ha hK (fun n hn => hno n ?_) ht
    exact Set.mem_Icc.mpr hn

/-- The weight `w_2` on a segment with no point of `Lℤ` is at most its larger endpoint value. -/
lemma gradWeightTwo_le_max_uIcc {s a K L p q t : ℝ} (hL : 0 < L) (hs1 : s < 1) (ha : 0 ≤ a)
    (hK : 1 ≤ K) (hno : ∀ n : ℤ, ¬(n * L ∈ uIcc p q)) (ht : t ∈ uIcc p q) :
    gradWeightTwo s a K L t ≤ max (gradWeightTwo s a K L p) (gradWeightTwo s a K L q) := by
  rcases le_total p q with hpq | hpq
  · rw [uIcc_of_le hpq] at ht hno
    refine gradWeightTwo_le_max_of_no_lattice hL hs1 ha hK (fun n hn => hno n ?_) ht
    exact Set.mem_Icc.mpr hn
  · rw [uIcc_of_ge hpq] at ht hno
    rw [max_comm]
    refine gradWeightTwo_le_max_of_no_lattice hL hs1 ha hK (fun n hn => hno n ?_) ht
    exact Set.mem_Icc.mpr hn

/-- A point of distance less than `1` has `w_1` equal to `max(d, K^{-1})^{-a}`. -/
lemma gradWeightOne_eq_of_lt_one {s a K L u : ℝ} (h : circDist L u < 1) :
    gradWeightOne s a K L u = max (circDist L u) K⁻¹ ^ (-a) := by
  unfold gradWeightOne
  simp only [h, ↓reduceIte]

/-- A point of distance at least `1` has `w_1` equal to `d^{s-2}`. -/
lemma gradWeightOne_eq_of_one_le {s a K L u : ℝ} (h : 1 ≤ circDist L u) :
    gradWeightOne s a K L u = circDist L u ^ (s - 2) := by
  unfold gradWeightOne
  simp only [show ¬ circDist L u < 1 from not_lt.mpr h, ↓reduceIte]

/-- A point of distance at least `1` has `w_2` equal to `d^{s-3}`. -/
lemma gradWeightTwo_eq_of_one_le {s a K L u : ℝ} (h : 1 ≤ circDist L u) :
    gradWeightTwo s a K L u = circDist L u ^ (s - 3) := by
  unfold gradWeightTwo
  simp only [show ¬ circDist L u < 1 from not_lt.mpr h, ↓reduceIte]

/-- Comparison of the weights: if `max(d, K^{-1}) ≤ lam`, then `w_1 ≤ lam w_2`. -/
lemma gradWeightOne_le_mul_gradWeightTwo {s a K L u lam : ℝ} (hK : 1 ≤ K) (hd : circDist L u ≤ lam) (hlam : K⁻¹ ≤ lam) :
    gradWeightOne s a K L u ≤ lam * gradWeightTwo s a K L u := by
  have hK0 : 0 < K⁻¹ := inv_pos.mpr (by linarith)
  by_cases h : circDist L u < 1
  · rw [gradWeightOne_eq_of_lt_one h]
    unfold gradWeightTwo
    simp only [h, ↓reduceIte]
    set M := max (circDist L u) K⁻¹ with hM
    have hMpos : 0 < M := lt_of_lt_of_le hK0 (le_max_right _ _)
    have hMle : M ≤ lam := max_le hd hlam
    have e : M ^ (-(1 + a)) = M ^ (-a) * M ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hMpos]; ring_nf
    have hM1 : M ^ (-1 : ℝ) * M = 1 := by
      rw [Real.rpow_neg_one, inv_mul_cancel₀ hMpos.ne']
    have hpos : 0 ≤ M ^ (-a) := Real.rpow_nonneg hMpos.le _
    rw [e]
    have hinv : 0 ≤ M ^ (-1 : ℝ) := Real.rpow_nonneg hMpos.le _
    have hw : M ^ (-a) = M ^ (-a) * (M ^ (-1 : ℝ) * M) := by rw [hM1, mul_one]
    calc M ^ (-a) = M ^ (-a) * (M ^ (-1 : ℝ) * M) := hw
      _ = (M ^ (-a) * M ^ (-1 : ℝ)) * M := by ring
      _ ≤ (M ^ (-a) * M ^ (-1 : ℝ)) * lam :=
          mul_le_mul_of_nonneg_left hMle (mul_nonneg hpos hinv)
      _ = lam * (M ^ (-a) * M ^ (-1 : ℝ)) := by ring
  · have h1 : 1 ≤ circDist L u := not_lt.mp h
    rw [gradWeightOne_eq_of_one_le h1, gradWeightTwo_eq_of_one_le h1]
    have hlam1 : 1 ≤ lam := le_trans h1 hd
    have hd0 : 0 < circDist L u := by linarith
    have e : circDist L u ^ (s - 2) = circDist L u * circDist L u ^ (s - 3) := by
      rw [show (s - 2) = (s - 3) + 1 by ring, Real.rpow_add hd0, Real.rpow_one]; ring
    have hpos : 0 ≤ circDist L u ^ (s - 3) := Real.rpow_nonneg hd0.le _
    rw [e]
    exact mul_le_mul_of_nonneg_right hd hpos

/-- The constant of the bound `|Z| ≤ C C_0 (w_1 + w_1)`. Only `s` and `a` enter. -/
noncomputable def gradZConst (a s : ℝ) : ℝ := 2 * (1 + 1 / (1 - a)) + 3 * (1 / (1 - s)) + 1

/-- A point of distance less than `1` has `w_1 ≥ 1`. -/
lemma one_le_gradWeightOne_of_lt_one {s a K L u : ℝ} (hK : 1 ≤ K) (ha : 0 ≤ a)
    (h : circDist L u < 1) : 1 ≤ gradWeightOne s a K L u := by
  rw [gradWeightOne_eq_of_lt_one h]
  have hK0 : 0 < K⁻¹ := inv_pos.mpr (by linarith)
  have hM : max (circDist L u) K⁻¹ ≤ 1 := max_le h.le (by rw [inv_le_one₀ (by linarith)]; linarith)
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (lt_of_lt_of_le hK0 (le_max_right _ _)) hM
    (by linarith)

/-- For `1 ≤ d ≤ lam`, one has `d^{s-1} ≤ lam d^{s-2}`. -/
lemma rpow_sub_one_le_mul_rpow_sub_two {s d lam : ℝ} (hd : 1 ≤ d) (hdl : d ≤ lam) :
    d ^ (s - 1) ≤ lam * d ^ (s - 2) := by
  have hd0 : 0 < d := by linarith
  have e : d ^ (s - 1) = d ^ (s - 2) * d := by
    rw [show (s - 1) = (s - 2) + 1 by ring, Real.rpow_add hd0, Real.rpow_one]
  rw [e, mul_comm lam]
  exact mul_le_mul_of_nonneg_left hdl (Real.rpow_nonneg hd0.le _)

/-- The differences part of Lemma 5.7, the case where both endpoints are at distance
at least `1` from `Lℤ` and the segment contains a point of `Lℤ`: the antipodal bound applies. -/
lemma abs_sub_le_gradZ_alpha {s a K L C0 : ℝ} {ψ : ℝ → ℝ} (hL : 0 < L) (hs0 : 0 < s)
    (hs1 : s < 1) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ L) (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t)
    {p q : ℝ} (hp1 : 1 ≤ circDist L p) (hq1 : 1 ≤ circDist L q)
    (hdp : circDist L p ≤ |q - p|) (hdq : circDist L q ≤ |q - p|) :
    |ψ q - ψ p| ≤ C0 / (1 - s) * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
  have hq := gradSplit_antipode_bound hs0 hs1 hL hC0 hψ hper hbd hq1
  have hp := gradSplit_antipode_bound hs0 hs1 hL hC0 hψ hper hbd hp1
  have htri := abs_sub_le (ψ q) (ψ (L / 2)) (ψ p)
  rw [abs_sub_comm (ψ (L / 2)) (ψ p)] at htri
  have hwq : C0 / (1 - s) * circDist L q ^ (s - 1) ≤ C0 / (1 - s) * (|q - p| * gradWeightOne s a K L q) := by
    rw [gradWeightOne_eq_of_one_le hq1]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hC0 (by linarith))
    exact rpow_sub_one_le_mul_rpow_sub_two hq1 hdq
  have hwp : C0 / (1 - s) * circDist L p ^ (s - 1) ≤ C0 / (1 - s) * (|q - p| * gradWeightOne s a K L p) := by
    rw [gradWeightOne_eq_of_one_le hp1]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hC0 (by linarith))
    exact rpow_sub_one_le_mul_rpow_sub_two hp1 hdp
  calc |ψ q - ψ p| ≤ |ψ q - ψ (L / 2)| + |ψ p - ψ (L / 2)| := htri
    _ ≤ C0 / (1 - s) * circDist L q ^ (s - 1) + C0 / (1 - s) * circDist L p ^ (s - 1) :=
        add_le_add hq hp
    _ ≤ C0 / (1 - s) * (|q - p| * gradWeightOne s a K L q) +
        C0 / (1 - s) * (|q - p| * gradWeightOne s a K L p) := add_le_add hwq hwp
    _ = C0 / (1 - s) * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by ring

/-- The differences part of Lemma 5.7, the case where one endpoint is within
distance `1` of `Lℤ`: both one-sided integrals from the origin are bounded in terms of the
segment length. -/
lemma abs_sub_le_gradZ_beta {s a K L C0 : ℝ} {ψ : ℝ → ℝ} (hL : 0 < L) (hs0 : 0 < s)
    (hs1 : s < 1) (ha1 : a < 1) (ha0 : 0 ≤ a) (hK : 1 ≤ K) (hC0 : 0 ≤ C0)
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ L)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t)
    {p q : ℝ} (hp1 : circDist L p < 1) (hdp : circDist L p ≤ |q - p|)
    (hdq : circDist L q ≤ |q - p|) :
    |ψ q - ψ p| ≤ 2 * ((1 + 1 / (1 - a)) + 1 / (1 - s)) * C0 * |q - p| *
      (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℝ, C1 = 1 + 1 / (1 - a) := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C2 : ℝ, C2 = C1 + 1 / (1 - s) := ⟨_, rfl⟩
  have hd1a : 0 ≤ 1 / (1 - a) := div_nonneg zero_le_one (by linarith)
  have hd1s : 0 ≤ 1 / (1 - s) := div_nonneg zero_le_one (by linarith)
  have hC1nn : 0 ≤ C1 := by rw [hC1]; linarith
  have hC12 : C1 ≤ C2 := by rw [hC2]; linarith
  have hC2nn : 0 ≤ C2 := le_trans hC1nn hC12
  have hwp1 : 1 ≤ gradWeightOne s a K L p := one_le_gradWeightOne_of_lt_one hK ha0 hp1
  have hwp0 : 0 ≤ gradWeightOne s a K L p := gradWeightOne_nonneg hK
  have hwq0 : 0 ≤ gradWeightOne s a K L q := gradWeightOne_nonneg hK
  have hlam0 : 0 ≤ |q - p| := abs_nonneg _
  have hdp_le : circDist L p ≤ L / 2 := circDist_le_half hL p
  have hdq_le : circDist L q ≤ L / 2 := circDist_le_half hL q
  -- the one-sided integral at `p`
  have hGp : gradWeightOneIntegral s a K L (circDist L p) ≤
      C1 * |q - p| * gradWeightOne s a K L p := by
    have h := gradWeightOneIntegral_le_of_le_one (s := s) hL ha1 hK (circDist_nonneg L p)
      (by linarith) hdp_le
    rw [gradWeightOne_eq_of_lt_one hp1, hC1]
    have hm : 0 ≤ max (circDist L p) K⁻¹ ^ (-a) :=
      Real.rpow_nonneg (le_trans (inv_pos.mpr (by linarith)).le (le_max_right _ _)) _
    calc gradWeightOneIntegral s a K L (circDist L p)
        ≤ (1 + 1 / (1 - a)) * circDist L p * max (circDist L p) K⁻¹ ^ (-a) := h
      _ ≤ (1 + 1 / (1 - a)) * |q - p| * max (circDist L p) K⁻¹ ^ (-a) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdp (by linarith)) hm
  -- the one-sided integral at `q`
  have hGq : gradWeightOneIntegral s a K L (circDist L q) ≤
      C2 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
    rcases lt_or_ge (circDist L q) 1 with hq1 | hq1
    · have h := gradWeightOneIntegral_le_of_le_one (s := s) hL ha1 hK (circDist_nonneg L q)
        hq1.le hdq_le
      have hGq' : gradWeightOneIntegral s a K L (circDist L q) ≤
          C1 * |q - p| * gradWeightOne s a K L q := by
        rw [gradWeightOne_eq_of_lt_one hq1, hC1]
        have hm : 0 ≤ max (circDist L q) K⁻¹ ^ (-a) :=
          Real.rpow_nonneg (le_trans (inv_pos.mpr (by linarith)).le (le_max_right _ _)) _
        calc gradWeightOneIntegral s a K L (circDist L q)
            ≤ (1 + 1 / (1 - a)) * circDist L q * max (circDist L q) K⁻¹ ^ (-a) := h
          _ ≤ (1 + 1 / (1 - a)) * |q - p| * max (circDist L q) K⁻¹ ^ (-a) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdq (by linarith)) hm
      have hcomb : C1 * |q - p| * gradWeightOne s a K L q ≤
          C2 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hC12) (mul_nonneg hlam0 hwq0),
          mul_nonneg hC2nn (mul_nonneg hlam0 hwp0)]
      exact le_trans hGq' hcomb
    · have h := gradWeightOneIntegral_le_const (s := s) hL ha1 hs0 hs1 hK (circDist_nonneg L q)
        hdq_le
      have hlam1 : 1 ≤ |q - p| := le_trans hq1 hdq
      have hprod : 1 ≤ |q - p| * gradWeightOne s a K L p := by nlinarith
      have hstep : C2 * 1 ≤ C2 * (|q - p| * gradWeightOne s a K L p) :=
        mul_le_mul_of_nonneg_left hprod hC2nn
      have hcomb : C2 * (|q - p| * gradWeightOne s a K L p) ≤
          C2 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
        nlinarith [mul_nonneg (mul_nonneg hC2nn hlam0) hwq0]
      calc gradWeightOneIntegral s a K L (circDist L q) ≤ C2 := by linarith
        _ ≤ C2 * (|q - p| * gradWeightOne s a K L p) := by linarith
        _ ≤ _ := hcomb
  -- the antipodal decomposition through the origin
  have harm := abs_sub_zero_le_arm (s := s) (a := a) hL hK hψ hper hbd
  have htri := abs_sub_le (ψ q) (ψ 0) (ψ p)
  have hCp : C1 * |q - p| * gradWeightOne s a K L p ≤
      C2 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC12) (mul_nonneg hlam0 hwp0),
      mul_nonneg hC2nn (mul_nonneg hlam0 hwq0)]
  have hGp' : C0 * gradWeightOneIntegral s a K L (circDist L p) ≤
      C0 * (C2 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q)) :=
    mul_le_mul_of_nonneg_left (le_trans hGp hCp) hC0
  have hGq' : C0 * gradWeightOneIntegral s a K L (circDist L q) ≤
      C0 * (C2 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q)) :=
    mul_le_mul_of_nonneg_left hGq hC0
  calc |ψ q - ψ p| ≤ |ψ q - ψ 0| + |ψ p - ψ 0| := by
        have := htri
        rwa [abs_sub_comm (ψ 0) (ψ p)] at this
    _ ≤ C0 * gradWeightOneIntegral s a K L (circDist L q) +
        C0 * gradWeightOneIntegral s a K L (circDist L p) :=
        add_le_add (harm q) (harm p)
    _ ≤ C0 * (C2 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q)) +
        C0 * (C2 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q)) :=
        add_le_add hGq' hGp'
    _ = 2 * ((1 + 1 / (1 - a)) + 1 / (1 - s)) * C0 * |q - p| *
        (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
        rw [hC2, hC1]; ring

/-- The one-sided bound for a segment with no point of `Lℤ`: the difference of the endpoint values
is at most `C_0 max(w_1(p), w_1(q)) |q - p|`. -/
lemma abs_sub_le_gradZ_no_lattice {s a K L C0 : ℝ} {ψ : ℝ → ℝ} (hL : 0 < L) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t) {p q : ℝ}
    (hno : ∀ n : ℤ, ¬(n * L ∈ uIcc p q)) :
    |ψ q - ψ p| ≤ C0 * max (gradWeightOne s a K L p) (gradWeightOne s a K L q) * |q - p| := by
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hFTC : ∫ t in p..q, deriv ψ t = ψ q - ψ p :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hψ.differentiable (by simp) t).hasDerivAt)
      (hcont.intervalIntegrable _ _)
  rw [← hFTC]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := q)
    (f := deriv ψ) (C := C0 * max (gradWeightOne s a K L p) (gradWeightOne s a K L q))
    (fun x hx => by
      have hxu : x ∈ uIcc p q := Set.uIoc_subset_uIcc hx
      rw [Real.norm_eq_abs]
      refine le_trans (hbd x) (mul_le_mul_of_nonneg_left ?_ hC0)
      exact gradWeightOne_le_max_uIcc hL hs1 ha0 hK hno hxu)
  rw [Real.norm_eq_abs] at hb
  exact hb

/-- The differences part of Lemma 5.7: the difference of the endpoint values of `ψ`
is bounded by the segment length times the averaged weight. -/
lemma abs_sub_le_gradZ {s a K L C0 : ℝ} {ψ : ℝ → ℝ} (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ L) (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t)
    (p q : ℝ) :
    |ψ q - ψ p| ≤ gradZConst a s * C0 * |q - p| *
      (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
  have hwp0 := gradWeightOne_nonneg (s := s) (a := a) (L := L) hK (u := p)
  have hwq0 := gradWeightOne_nonneg (s := s) (a := a) (L := L) hK (u := q)
  have hK1 : 1 ≤ 1 / (1 - s) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hC1 : 0 ≤ 1 / (1 - a) := div_nonneg zero_le_one (by linarith)
  have hk : 0 ≤ 1 / (1 - s) := div_nonneg zero_le_one (by linarith)
  have hgc : 1 ≤ gradZConst a s := by
    unfold gradZConst; linarith
  have hsum : 0 ≤ gradWeightOne s a K L p + gradWeightOne s a K L q := by linarith
  rcases eq_or_ne p q with rfl | hpq
  · simp
  · by_cases hc : ∃ n : ℤ, (n : ℝ) * L ∈ uIcc p q
    · obtain ⟨n, hn⟩ := hc
      have hlam : 0 < |q - p| := abs_pos.mpr (sub_ne_zero.mpr hpq.symm)
      have hdp : circDist L p ≤ |q - p| :=
        le_trans (circDist_le_abs_sub_int_mul hL p n) (abs_sub_le_of_mem_uIcc left_mem_uIcc hn)
      have hdq : circDist L q ≤ |q - p| :=
        le_trans (circDist_le_abs_sub_int_mul hL q n) (abs_sub_le_of_mem_uIcc right_mem_uIcc hn)
      by_cases hp1 : circDist L p < 1
      · have h := abs_sub_le_gradZ_beta (s := s) (a := a) (K := K) (C0 := C0) hL hs0 hs1 ha1 ha0
          hK hC0 hψ hper hbd hp1 hdp hdq
        have hC : 2 * ((1 + 1 / (1 - a)) + 1 / (1 - s)) ≤ gradZConst a s := by
          unfold gradZConst; linarith
        calc |ψ q - ψ p| ≤ 2 * ((1 + 1 / (1 - a)) + 1 / (1 - s)) * C0 * |q - p| *
              (gradWeightOne s a K L p + gradWeightOne s a K L q) := h
          _ ≤ gradZConst a s * C0 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
              apply mul_le_mul_of_nonneg_right _ hsum
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              exact mul_le_mul_of_nonneg_right hC hC0
      · by_cases hq1 : circDist L q < 1
        · have h := abs_sub_le_gradZ_beta (s := s) (a := a) (K := K) (C0 := C0) hL hs0 hs1 ha1 ha0
            hK hC0 hψ hper hbd hq1 (by rw [abs_sub_comm]; exact hdq) (by rw [abs_sub_comm]; exact hdp)
          have hC : 2 * ((1 + 1 / (1 - a)) + 1 / (1 - s)) ≤ gradZConst a s := by
            unfold gradZConst; linarith
          have e1 : |ψ q - ψ p| = |ψ p - ψ q| := abs_sub_comm _ _
          have e2 : |p - q| = |q - p| := abs_sub_comm _ _
          have hsum' : gradWeightOne s a K L q + gradWeightOne s a K L p =
              gradWeightOne s a K L p + gradWeightOne s a K L q := add_comm _ _
          rw [e1]
          rw [e2, hsum'] at h
          calc |ψ p - ψ q| ≤ 2 * ((1 + 1 / (1 - a)) + 1 / (1 - s)) * C0 * |q - p| *
                (gradWeightOne s a K L p + gradWeightOne s a K L q) := h
            _ ≤ gradZConst a s * C0 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
                apply mul_le_mul_of_nonneg_right _ hsum
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                exact mul_le_mul_of_nonneg_right hC hC0
        · have hα := abs_sub_le_gradZ_alpha (s := s) (a := a) (K := K) (C0 := C0) hL hs0 hs1 hC0
            hψ hper hbd (not_lt.mp hp1) (not_lt.mp hq1) hdp hdq
          calc |ψ q - ψ p| ≤ C0 / (1 - s) * |q - p| *
                (gradWeightOne s a K L p + gradWeightOne s a K L q) := hα
            _ ≤ gradZConst a s * C0 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
                apply mul_le_mul_of_nonneg_right _ hsum
                have hC : C0 / (1 - s) ≤ gradZConst a s * C0 := by
                  rw [div_eq_mul_one_div]
                  have : 1 / (1 - s) ≤ gradZConst a s := by unfold gradZConst; linarith
                  nlinarith
                exact mul_le_mul_of_nonneg_right hC (abs_nonneg _) |>.trans_eq (by ring)
    · have hno : ∀ n : ℤ, ¬(n * L ∈ uIcc p q) := fun n hn => hc ⟨n, hn⟩
      have h := abs_sub_le_gradZ_no_lattice (s := s) (a := a) (K := K) (C0 := C0) hL hs1 ha0 hK hC0
        hψ hbd hno
      have hmax : max (gradWeightOne s a K L p) (gradWeightOne s a K L q) ≤
          gradWeightOne s a K L p + gradWeightOne s a K L q := max_le (by linarith) (by linarith)
      calc |ψ q - ψ p| ≤ C0 * max (gradWeightOne s a K L p) (gradWeightOne s a K L q) * |q - p| := h
        _ ≤ C0 * (gradWeightOne s a K L p + gradWeightOne s a K L q) * |q - p| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hmax hC0
        _ ≤ gradZConst a s * C0 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
            have : C0 * (gradWeightOne s a K L p + gradWeightOne s a K L q) * |q - p| ≤
                gradZConst a s * C0 * |q - p| * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
              have h1 : 0 ≤ C0 * (gradWeightOne s a K L p + gradWeightOne s a K L q) * |q - p| :=
                mul_nonneg (mul_nonneg hC0 hsum) (abs_nonneg _)
              nlinarith [mul_nonneg (mul_nonneg hC0 (abs_nonneg (q - p))) hsum]
            exact this

/-- The differences part of Lemma 5.7, the bound `|Z| ≤ C C_0 (w_1(p) + w_1(q))` in the
variable `u = x/ℓ`, with `C = gradZConst a s` depending only on `s` and `a`. -/
lemma gradZavg_abs_le {s a K L C0 : ℝ} {ψ : ℝ → ℝ} (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ L) (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t)
    (p q : ℝ) :
    |gradZavg ψ p q| ≤ gradZConst a s * C0 * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
  have hwp0 := gradWeightOne_nonneg (s := s) (a := a) (L := L) hK (u := p)
  have hwq0 := gradWeightOne_nonneg (s := s) (a := a) (L := L) hK (u := q)
  have hgc : 1 ≤ gradZConst a s := by
    unfold gradZConst
    have : 0 ≤ 1 / (1 - a) := div_nonneg zero_le_one (by linarith)
    have : 0 ≤ 1 / (1 - s) := div_nonneg zero_le_one (by linarith)
    linarith
  rcases eq_or_ne p q with rfl | hpq
  · have hz : gradZavg ψ p p = deriv ψ p := by
      unfold gradZavg
      simp
    rw [hz]
    have hb := hbd p
    have : C0 * gradWeightOne s a K L p ≤ gradZConst a s * C0 * (gradWeightOne s a K L p + gradWeightOne s a K L p) := by
      nlinarith [mul_nonneg hC0 hwp0, mul_nonneg (mul_nonneg hC0 hwp0) (sub_nonneg.mpr hgc)]
    exact le_trans hb this
  · have hlam : 0 < |q - p| := abs_pos.mpr (sub_ne_zero.mpr hpq.symm)
    rw [gradZavg_eq_div hψ hpq, abs_div, div_le_iff₀ hlam]
    have h := abs_sub_le_gradZ hL hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd p q
    calc |ψ q - ψ p| ≤ gradZConst a s * C0 * |q - p| *
          (gradWeightOne s a K L p + gradWeightOne s a K L q) := h
      _ = gradZConst a s * C0 * (gradWeightOne s a K L p + gradWeightOne s a K L q) * |q - p| := by ring

/-- The derivative increment bound: if `|ψ''| ≤ M` on the segment between `p` and `t`, then
`|ψ'(t) - ψ'(p)| ≤ M |t - p|`, for `M ≥ 0` and `|t - p| ≤` the length of a segment containing it. -/
lemma gradDeriv_sub_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {M p t : ℝ} (hM : ∀ τ ∈ uIcc p t,
    |deriv (deriv ψ) τ| ≤ M) : |deriv ψ t - deriv ψ p| ≤ M * |t - p| := by
  have hd1 : ContDiff ℝ ∞ (deriv ψ) := hψ.deriv'
  have hcont2 : Continuous (deriv (deriv ψ)) := hd1.continuous_deriv (by simp)
  have hFTC : ∫ τ in p..t, deriv (deriv ψ) τ = deriv ψ t - deriv ψ p :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun τ _ => (hd1.differentiable (by simp) τ).hasDerivAt)
      (hcont2.intervalIntegrable _ _)
  rw [← hFTC]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := t)
    (f := deriv (deriv ψ)) (C := M)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact hM x (Set.uIoc_subset_uIcc hx))
  rw [Real.norm_eq_abs] at hb
  exact hb

/-- A point of the form `p + θ(q - p)` with `θ ∈ [0, 1]` lies in `uIcc p q`. -/
lemma mem_uIcc_segment {p q θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : p + θ * (q - p) ∈ uIcc p q := by
  rcases le_total p q with hpq | hpq
  · rw [uIcc_of_le hpq, Set.mem_Icc]
    constructor <;> nlinarith
  · rw [uIcc_of_ge hpq, Set.mem_Icc]
    constructor <;> nlinarith

/-- Core bound: if `|ψ''| ≤ M` on `uIcc p q` (with `M ≥ 0`), then `|Z - ψ'(p)| ≤ M |q - p|`. -/
lemma gradZavg_sub_deriv_core {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {M p q : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ τ ∈ uIcc p q, |deriv (deriv ψ) τ| ≤ M) :
    |gradZavg ψ p q - deriv ψ p| ≤ M * |q - p| := by
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hint : IntervalIntegrable (fun θ : ℝ => deriv ψ (p + θ * (q - p))) volume 0 1 :=
    (hcont.comp (continuous_const.add (continuous_id.mul continuous_const))).intervalIntegrable _ _
  have hsplit : gradZavg ψ p q - deriv ψ p =
      ∫ θ in (0 : ℝ)..1, (deriv ψ (p + θ * (q - p)) - deriv ψ p) := by
    unfold gradZavg
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp
  rw [hsplit]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun θ : ℝ => deriv ψ (p + θ * (q - p)) - deriv ψ p) (C := M * |q - p|)
    (fun θ hθ => by
      have hθ' : θ ∈ uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc hθ
      rw [uIcc_of_le zero_le_one, Set.mem_Icc] at hθ'
      rw [Real.norm_eq_abs]
      have hmem : p + θ * (q - p) ∈ uIcc p q := mem_uIcc_segment hθ'.1 hθ'.2
      have hsub : uIcc p (p + θ * (q - p)) ⊆ uIcc p q :=
        Set.uIcc_subset_uIcc left_mem_uIcc hmem
      have h1 := gradDeriv_sub_le hψ (M := M) (p := p) (t := p + θ * (q - p))
        (fun τ hτ => hM τ (hsub hτ))
      have hlen : |p + θ * (q - p) - p| ≤ |q - p| := by
        rw [show p + θ * (q - p) - p = θ * (q - p) by ring, abs_mul,
          abs_of_nonneg hθ'.1]
        exact mul_le_of_le_one_left (abs_nonneg _) hθ'.2
      calc |deriv ψ (p + θ * (q - p)) - deriv ψ p|
          ≤ M * |p + θ * (q - p) - p| := h1
        _ ≤ M * |q - p| := mul_le_mul_of_nonneg_left hlen hM0)
  rw [Real.norm_eq_abs] at hb
  have e : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [e, mul_one] at hb
  exact hb

/-- The non-crossing bound: for a segment `[p, q]` with no point of `Lℤ`, the bound of
`gradZavg_sub_deriv_core` holds with `M = C_0 max(w_2(p), w_2(q))`. -/
lemma gradZavg_sub_deriv_no_lattice {s a K L C0 : ℝ} {ψ : ℝ → ℝ} (hL : 0 < L) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hψ : ContDiff ℝ ∞ ψ)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s a K L t) {p q : ℝ}
    (hno : ∀ n : ℤ, ¬(n * L ∈ uIcc p q)) :
    |gradZavg ψ p q - deriv ψ p| ≤ C0 * max (gradWeightTwo s a K L p) (gradWeightTwo s a K L q) * |q - p| := by
  have hw2p := gradWeightTwo_nonneg (s := s) (a := a) (L := L) hK (u := p)
  have hw2q := gradWeightTwo_nonneg (s := s) (a := a) (L := L) hK (u := q)
  refine gradZavg_sub_deriv_core hψ (by positivity) (fun τ hτ => ?_)
  calc |deriv (deriv ψ) τ| ≤ C0 * gradWeightTwo s a K L τ := hbd2 τ
    _ ≤ C0 * max (gradWeightTwo s a K L p) (gradWeightTwo s a K L q) :=
        mul_le_mul_of_nonneg_left (gradWeightTwo_le_max_uIcc hL hs1 ha0 hK hno hτ) hC0

/-- The differences part of Lemma 5.7, the bound `|Z - ψ'(p)| ≤ C λ C_0 (w_2(p) + w_2(q))`
in the variable `u = x/ℓ`, with `λ = |q - p|` and `C = gradZConst a s + 1`. -/
lemma gradZavg_sub_deriv_le {s a K L C0 : ℝ} {ψ : ℝ → ℝ} (hL : 0 < L) (hs0 : 0 < s)
    (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1) (hK : 1 ≤ K) (hC0 : 0 ≤ C0)
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ L)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s a K L t) (p q : ℝ) :
    |gradZavg ψ p q - deriv ψ p| ≤
      (gradZConst a s + 1) * C0 * |q - p| * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) := by
  have hw2p := gradWeightTwo_nonneg (s := s) (a := a) (L := L) hK (u := p)
  have hw2q := gradWeightTwo_nonneg (s := s) (a := a) (L := L) hK (u := q)
  have hgc : 1 ≤ gradZConst a s := by
    unfold gradZConst
    have : 0 ≤ 1 / (1 - a) := div_nonneg zero_le_one (by linarith)
    have : 0 ≤ 1 / (1 - s) := div_nonneg zero_le_one (by linarith)
    linarith
  have hCW : 0 ≤ (gradZConst a s + 1) * C0 := mul_nonneg (by linarith) hC0
  rcases eq_or_ne p q with rfl | hpq
  · have hz : gradZavg ψ p p = deriv ψ p := by
      unfold gradZavg
      simp
    rw [hz]
    simp
  · by_cases hc : ∃ n : ℤ, (n : ℝ) * L ∈ uIcc p q
    · obtain ⟨n, hn⟩ := hc
      have hlam : 0 < |q - p| := abs_pos.mpr (sub_ne_zero.mpr hpq.symm)
      have hdp : circDist L p ≤ |q - p| :=
        le_trans (circDist_le_abs_sub_int_mul hL p n) (abs_sub_le_of_mem_uIcc left_mem_uIcc hn)
      have hdq : circDist L q ≤ |q - p| :=
        le_trans (circDist_le_abs_sub_int_mul hL q n) (abs_sub_le_of_mem_uIcc right_mem_uIcc hn)
      by_cases hK' : K⁻¹ ≤ |q - p|
      · -- the segment is long compared to the microscopic scale: use `Z` and `w_1 ≤ λ w_2`
        have h1 := gradZavg_abs_le (s := s) (a := a) hL hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd p q
        have hbp := hbd p
        have hw1p := gradWeightOne_le_mul_gradWeightTwo (s := s) (a := a) (L := L) (u := p)
          (lam := |q - p|) hK hdp hK'
        have hw1q := gradWeightOne_le_mul_gradWeightTwo (s := s) (a := a) (L := L) (u := q)
          (lam := |q - p|) hK hdq hK'
        have hw1p0 := gradWeightOne_nonneg (s := s) (a := a) (L := L) hK (u := p)
        have hw1q0 := gradWeightOne_nonneg (s := s) (a := a) (L := L) hK (u := q)
        have hsum : gradWeightOne s a K L p + gradWeightOne s a K L q ≤
            |q - p| * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) := by
          rw [mul_add]; linarith
        calc |gradZavg ψ p q - deriv ψ p| ≤ |gradZavg ψ p q| + |deriv ψ p| := abs_sub _ _
          _ ≤ gradZConst a s * C0 * (gradWeightOne s a K L p + gradWeightOne s a K L q) +
              C0 * gradWeightOne s a K L p := add_le_add h1 hbp
          _ ≤ (gradZConst a s + 1) * C0 * (gradWeightOne s a K L p + gradWeightOne s a K L q) := by
              nlinarith [mul_nonneg hC0 hw1p0, mul_nonneg hC0 hw1q0]
          _ ≤ (gradZConst a s + 1) * C0 * (|q - p| * (gradWeightTwo s a K L p + gradWeightTwo s a K L q)) :=
              mul_le_mul_of_nonneg_left hsum hCW
          _ = (gradZConst a s + 1) * C0 * |q - p| * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) := by
              ring
      · -- the segment is short compared to the microscopic scale: use `|ψ''| ≤ C_0 K^{1+a}`
        have hlt : |q - p| < K⁻¹ := not_le.mp hK'
        have hK0 : 0 < K := by linarith
        have hdlt1 : circDist L p < 1 :=
          lt_of_le_of_lt hdp (lt_of_lt_of_le hlt (inv_le_one_of_one_le₀ hK))
        have heq2p : gradWeightTwo s a K L p = K ^ (1 + a) := by
          unfold gradWeightTwo
          simp only [hdlt1, ↓reduceIte]
          rw [max_eq_right (le_trans hdp hlt.le), Real.inv_rpow hK0.le, Real.rpow_neg hK0.le,
            inv_inv]
        have hM : |gradZavg ψ p q - deriv ψ p| ≤ C0 * K ^ (1 + a) * |q - p| :=
          gradZavg_sub_deriv_core (p := p) (q := q) hψ (M := C0 * K ^ (1 + a))
          (mul_nonneg hC0 (Real.rpow_nonneg hK0.le _))
          (fun τ _ => by
            calc |deriv (deriv ψ) τ| ≤ C0 * gradWeightTwo s a K L τ := hbd2 τ
              _ ≤ C0 * K ^ (1 + a) := mul_le_mul_of_nonneg_left
                  (gradWeightTwo_le_K_pow hs1 ha0 hK) hC0)
        calc |gradZavg ψ p q - deriv ψ p| ≤ C0 * K ^ (1 + a) * |q - p| := hM
          _ = C0 * gradWeightTwo s a K L p * |q - p| := by rw [heq2p]
          _ ≤ (gradZConst a s + 1) * C0 * |q - p| * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) := by
              have h3 : C0 * gradWeightTwo s a K L p * |q - p| ≤
                  C0 * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) * |q - p| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                exact mul_le_mul_of_nonneg_left (by linarith) hC0
              have h4 : C0 * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) * |q - p| ≤
                  (gradZConst a s + 1) * C0 * |q - p| * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) := by
                nlinarith [mul_nonneg (mul_nonneg hC0 hw2p) (abs_nonneg (q - p)),
                  mul_nonneg (mul_nonneg hC0 hw2q) (abs_nonneg (q - p)),
                  mul_nonneg (mul_nonneg hCW (abs_nonneg (q - p))) (add_nonneg hw2p hw2q)]
              linarith
    · have hno : ∀ n : ℤ, ¬(n * L ∈ uIcc p q) := fun n hn => hc ⟨n, hn⟩
      have h := gradZavg_sub_deriv_no_lattice (s := s) (a := a) (K := K) (C0 := C0) hL hs1 ha0 hK hC0
        hψ hbd2 hno
      have hmax : max (gradWeightTwo s a K L p) (gradWeightTwo s a K L q) ≤
          gradWeightTwo s a K L p + gradWeightTwo s a K L q := max_le (by linarith) (by linarith)
      calc |gradZavg ψ p q - deriv ψ p|
          ≤ C0 * max (gradWeightTwo s a K L p) (gradWeightTwo s a K L q) * |q - p| := h
        _ ≤ C0 * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) * |q - p| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hC0) (abs_nonneg _)
        _ ≤ (gradZConst a s + 1) * C0 * |q - p| * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) := by
            nlinarith [mul_nonneg (mul_nonneg hC0 (abs_nonneg (q - p))) (add_nonneg hw2p hw2q)]

/-- The same bound at the other endpoint: `|Z - ψ'(q)| ≤ (C + 1) C_0 |q - p| (w_2(p) + w_2(q))`. -/
lemma gradZavg_sub_deriv_le_right {s a K L C0 : ℝ} {ψ : ℝ → ℝ} (hL : 0 < L) (hs0 : 0 < s)
    (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1) (hK : 1 ≤ K) (hC0 : 0 ≤ C0)
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ L)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t)
    (hbd2 : ∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s a K L t) (p q : ℝ) :
    |gradZavg ψ p q - deriv ψ q| ≤
      (gradZConst a s + 1) * C0 * |q - p| * (gradWeightTwo s a K L p + gradWeightTwo s a K L q) := by
  have h := gradZavg_sub_deriv_le hL hs0 hs1 ha0 ha1 hK hC0 hψ hper hbd hbd2 q p
  rw [gradZavg_symm ψ q p, abs_sub_comm p q, add_comm (gradWeightTwo s a K L q)] at h
  exact h

end Riesz1

end
