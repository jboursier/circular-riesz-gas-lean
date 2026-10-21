/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaledLattice

/-!
# Locally uniform convergence of the scaled symmetric sums

The symmetric sums `∑_{|k| ≤ M} sgn(r - kL)|r - kL|^{s-1}` converge to `K_{s,L}(r)` locally uniformly
off the lattice `L ℤ`. The proof pairs the terms
`k` and `-k`. On a bounded set `|t| ≤ R` the pair with index `j` is at most
`2(1-s) R ((j+1)/2)^{s-2}` as soon as `j + 1 ≥ 2R`, and these bounds are summable. Hence the
symmetric sums are uniformly Cauchy on every bounded set, which gives uniform convergence on each
compact subset of the complement of `ℤ` at unit scale. Rescaling transfers this to `L ℤ`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The pair `φ(t-u) + φ(t+u)` for `φ = signPow s`, when `|t| ≤ R ≤ u/2`, is bounded by
`2(1-s) R (u/2)^{s-2}`. -/
lemma abs_signPow_pair_le_of_abs_le {s t R u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht : |t| ≤ R)
    (hu : 2 * R ≤ u) (hu0 : 0 < u) :
    |signPow s (t - u) + signPow s (t + u)| ≤ 2 * (1 - s) * R * (u / 2) ^ (s - 2) := by
  have e : t - u = -(u - t) := by ring
  have hc : 0 < u / 2 := by positivity
  have ha : u / 2 ≤ u - t := by linarith [le_abs_self t]
  have hb : u / 2 ≤ t + u := by linarith [neg_abs_le t]
  have hmvt := abs_signPow_sub_le_of_le hs0 hs1 hc ha hb
  have hpair : signPow s (t - u) + signPow s (t + u) =
      signPow s (t + u) - signPow s (u - t) := by
    rw [e, signPow_neg']
    ring
  have h2 : |(t + u) - (u - t)| ≤ 2 * R := by
    rw [show (t + u) - (u - t) = 2 * t by ring, abs_mul, abs_two]
    linarith
  have hpow : 0 ≤ (1 - s) * (u / 2) ^ (s - 2) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  calc |signPow s (t - u) + signPow s (t + u)|
      = |signPow s (t + u) - signPow s (u - t)| := by rw [hpair]
    _ ≤ (1 - s) * (u / 2) ^ (s - 2) * |(t + u) - (u - t)| := hmvt
    _ ≤ (1 - s) * (u / 2) ^ (s - 2) * (2 * R) := mul_le_mul_of_nonneg_left h2 hpow
    _ = 2 * (1 - s) * R * (u / 2) ^ (s - 2) := by ring

/-- The summable majorant `2(1-s) R (j+1)^{s-2} / 2^{s-2}` of the pair bounds, indexed by `j ∈ ℕ`. -/
lemma summable_pairMajorant {s R : ℝ} (hs1 : s < 1) :
    Summable (fun j : ℕ => 2 * (1 - s) * R * (((j : ℝ) + 1) ^ (s - 2) / 2 ^ (s - 2))) := by
  have h1 : Summable (fun j : ℕ => (j : ℝ) ^ (s - 2)) := Real.summable_nat_rpow.2 (by linarith)
  have h2 : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ)) ^ (s - 2)) :=
    (summable_nat_add_iff 1).2 h1
  have h3 : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (s - 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using h2
  exact (h3.div_const _).mul_left _

/-- The pair with index `j` is bounded by the majorant once `2R ≤ j + 1`. -/
lemma abs_pairTerm_le_majorant {s t R : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht : |t| ≤ R) (j : ℕ)
    (hj : 2 * R ≤ (j : ℝ) + 1) :
    |pairTerm s t j| ≤ 2 * (1 - s) * R * (((j : ℝ) + 1) ^ (s - 2) / 2 ^ (s - 2)) := by
  have h := abs_signPow_pair_le_of_abs_le hs0 hs1 ht hj (by positivity)
  have hdiv := Real.div_rpow (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1) (by norm_num : (0 : ℝ) ≤ 2)
    (s - 2)
  unfold pairTerm
  rw [hdiv] at h
  exact h

/-- **Tail bound for the symmetric sums.** For `|t| ≤ R` and `⌈2R⌉₊ ≤ n ≤ m`, the difference of
the symmetric sums of orders `m` and `n` is bounded by the tail of the majorant beyond `n`. -/
lemma abs_symmetric_sum_sub_le {s R t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht : |t| ≤ R)
    {n m : ℕ} (hnm : n ≤ m) (hn : ⌈2 * R⌉₊ ≤ n) :
    |(∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), signPow s (t - k)) -
        ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), signPow s (t - k)| ≤
      ∑' k : ℕ, 2 * (1 - s) * R * ((((k + n : ℕ) : ℝ) + 1) ^ (s - 2) / 2 ^ (s - 2)) := by
  have hR : 0 ≤ R := le_trans (abs_nonneg t) ht
  rw [symmetric_eq_add_pairs s t m, symmetric_eq_add_pairs s t n, add_sub_add_left_eq_sub,
    ← Finset.sum_Ico_eq_sub _ hnm]
  have hsumm : Summable (fun k : ℕ => 2 * (1 - s) * R *
      ((((k + n : ℕ) : ℝ) + 1) ^ (s - 2) / 2 ^ (s - 2))) :=
    (summable_nat_add_iff n).2 (summable_pairMajorant (R := R) hs1)
  have hterm : ∀ j ∈ Finset.Ico n m, 2 * R ≤ (j : ℝ) + 1 := by
    intro j hj
    have hnj : n ≤ j := (Finset.mem_Ico.1 hj).1
    have h1 : (⌈2 * R⌉₊ : ℝ) ≤ j := by exact_mod_cast hn.trans hnj
    have h2 : 2 * R ≤ (⌈2 * R⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hnonneg : ∀ k : ℕ, 0 ≤ 2 * (1 - s) * R *
      ((((k + n : ℕ) : ℝ) + 1) ^ (s - 2) / 2 ^ (s - 2)) := fun k =>
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hR)
      (div_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _))
  calc |∑ j ∈ Finset.Ico n m, pairTerm s t j|
      ≤ ∑ j ∈ Finset.Ico n m, |pairTerm s t j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Ico n m, 2 * (1 - s) * R * (((j : ℝ) + 1) ^ (s - 2) / 2 ^ (s - 2)) :=
        Finset.sum_le_sum fun j hj => abs_pairTerm_le_majorant hs0 hs1 ht j (hterm j hj)
    _ = ∑ k ∈ Finset.range (m - n), 2 * (1 - s) * R *
          ((((k + n : ℕ) : ℝ) + 1) ^ (s - 2) / 2 ^ (s - 2)) := by
        rw [Finset.sum_Ico_eq_sum_range]
        exact Finset.sum_congr rfl fun k _ => by simp only [add_comm n k]
    _ ≤ ∑' k : ℕ, 2 * (1 - s) * R * ((((k + n : ℕ) : ℝ) + 1) ^ (s - 2) / 2 ^ (s - 2)) :=
        Summable.sum_le_tsum _ (fun k _ => hnonneg k) hsumm

/-- **Uniform Cauchy property of the symmetric sums on bounded sets.** For every `ε > 0` there is
`N` such that the symmetric sums of orders `m, n ≥ N` differ by less than `ε` at every `|t| ≤ R`.
The bound holds on all of `[-R, R]`, including the integers. -/
lemma symmetric_signPow_uniformCauchy {s R : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ t : ℝ, |t| ≤ R →
      |(∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), signPow s (t - k)) -
        ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), signPow s (t - k)| < ε := by
  have hT := tendsto_sum_nat_add (fun j : ℕ => 2 * (1 - s) * R *
    (((j : ℝ) + 1) ^ (s - 2) / 2 ^ (s - 2)))
  have hev := ((tendsto_order.1 hT).2 ε hε)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  refine ⟨max ⌈2 * R⌉₊ N1, fun m hm n hn t ht => ?_⟩
  have hm1 : ⌈2 * R⌉₊ ≤ m := le_trans (le_max_left _ _) hm
  have hn1 : ⌈2 * R⌉₊ ≤ n := le_trans (le_max_left _ _) hn
  have hm2 : N1 ≤ m := le_trans (le_max_right _ _) hm
  have hn2 : N1 ≤ n := le_trans (le_max_right _ _) hn
  rcases le_total n m with h | h
  · exact lt_of_le_of_lt (abs_symmetric_sum_sub_le hs0 hs1 ht h hn1)
      (hN1 n hn2)
  · rw [abs_sub_comm]
    exact lt_of_le_of_lt (abs_symmetric_sum_sub_le hs0 hs1 ht h hm1) (hN1 m hm2)

/-- **Uniform convergence of the unit symmetric sums on compact subsets of `ℝ ∖ ℤ`.** -/
lemma tendstoUniformlyOn_symmetric_signPow {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {K : Set ℝ}
    (hK : IsCompact K) (hKs : K ⊆ {t : ℝ | ∀ k : ℤ, t ≠ k}) :
    TendstoUniformlyOn (fun (M : ℕ) (t : ℝ) =>
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k)) (periodicKernel s) atTop K := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := fun t : ℝ => t) continuousOn_id
  have hbd : ∀ t ∈ K, |t| ≤ max R 0 := fun t ht =>
    (by have := hR t ht; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _))
  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
  · rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := symmetric_signPow_uniformCauchy hs0 hs1 hε
    refine ⟨N, fun m hm n hn t ht => ?_⟩
    rw [Real.dist_eq]
    exact hN m hm n hn t (hbd t ht)
  · intro t ht
    exact tendsto_symmetric_signPow hs0 hs1 (hKs ht)

/-- **Locally uniform convergence of the scaled symmetric sums**.
The partial sums `∑_{|k| ≤ M} sgn(r - kL)|r - kL|^{s-1}` converge to `K_{s,L}(r)` uniformly on
every compact subset of `{r | ∀ k, r ≠ kL}`. -/
theorem tendstoLocallyUniformlyOn_scaled_signPow {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hL : 0 < L) :
    TendstoLocallyUniformlyOn (fun (M : ℕ) (r : ℝ) =>
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r - k * L))
      (scaledKernel s L) atTop {r : ℝ | ∀ k : ℤ, r ≠ k * L} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_lattice_compl hL)]
  intro K hKs hK
  have hK' : IsCompact ((fun r : ℝ => r / L) '' K) := hK.image (continuous_id.div_const L)
  have hKs' : (fun r : ℝ => r / L) '' K ⊆ {t : ℝ | ∀ k : ℤ, t ≠ k} := by
    rintro _ ⟨r, hr, rfl⟩ k h
    exact hKs hr k (by rw [div_eq_iff hL.ne'] at h; linarith)
  have hU := tendstoUniformlyOn_symmetric_signPow hs0 hs1 hK' hKs'
  rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
  intro ε hε
  have hpos : 0 < L ^ (s - 1) := Real.rpow_pos_of_pos hL _
  filter_upwards [hU (ε / L ^ (s - 1)) (div_pos hε hpos)] with M hM
  intro r hr
  have h := hM (r / L) ⟨r, hr, rfl⟩
  rw [scaledKernel_eq_periodic hs0 hs1 hL (hKs hr), signPow_scaled_sum hL M, dist_eq_norm,
    ← mul_sub, norm_mul, Real.norm_of_nonneg hpos.le]
  rw [dist_eq_norm] at h
  calc L ^ (s - 1) * ‖periodicKernel s (r / L) -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r / L - k)‖
      < L ^ (s - 1) * (ε / L ^ (s - 1)) := mul_lt_mul_of_pos_left h hpos
    _ = ε := by field_simp

end Riesz1
