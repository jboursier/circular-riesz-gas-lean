/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsLpPair
public import Riesz1.Auxiliary.LoopArcsLpMeasure

/-!
# Summing the pair term over lifts

The arcs part of Lemma B.2, small region. The pair integrand of
`Riesz1.pairIntegrand` is summed over all lifts `z_i + nN` and `z_j + n'N` of pairs of particles.
The window `(m - 1, m + 1)` of the left lift selects the particles `i` counted by the rooted
energy `E_i = Riesz1.rootedEnergy`. This is the combinatorial step of the small-region estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal

namespace Riesz1

attribute [local instance] Classical.propDecidable

/-- If the left lift lies outside the window `(m - 1, m + 1)`, then the pair integral vanishes. -/
theorem lintegral_pairIntegrand_eq_zero_of_not_window {s : ℝ} (hs0 : 0 < s) (m ℓ₁ ℓ₂ : ℝ)
    (h : ¬ (m - 1 < ℓ₁ ∧ ℓ₁ < m + 1)) :
    ∫⁻ t in Ioc m (m + 1), ∫⁻ u, ∫⁻ v, pairIntegrand s ℓ₁ ℓ₂ t u v = 0 := by
  refine nonpos_iff_eq_zero.mp ((lintegral_pairIntegrand_le hs0 m ℓ₁ ℓ₂).trans ?_)
  rw [ite_eq_right (fun hc => h hc.1)]

/-- For a fixed left lift in the window `(m - 1, m + 1)`, the sum over the lifts of the second
particle `j` has at most one nonzero term, and it is bounded by the rooted-energy term of `j`. -/
theorem tsum_lift_pairIntegrand_le {s : ℝ} (hs0 : 0 < s) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (X : Configuration N) (m : ℝ) (i j : Fin (N : ℕ)) (n : ℤ)
    (hn1 : m - 1 < loopArcPos N X i + n * N) (hn2 : loopArcPos N X i + n * N < m + 1) :
    ∑' n' : ℤ, ∫⁻ t in Ioc m (m + 1), ∫⁻ u, ∫⁻ v,
        pairIntegrand s (loopArcPos N X i + n * N) (loopArcPos N X j + n' * N) t u v
      ≤ if j ≠ i ∧ dist (loopPos X i) (loopPos X j) ≤ 3 then
          ENNReal.ofReal (((s + 1) * (s + 2))⁻¹) *
            ENNReal.ofReal (dist (loopPos X i) (loopPos X j) ^ (-s)) else 0 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hbound := fun n' : ℤ => lintegral_pairIntegrand_le hs0 m
    (loopArcPos N X i + n * N) (loopArcPos N X j + n' * N)
  by_cases hex : ∃ n1 : ℤ,
      0 < loopArcPos N X j + n1 * N - (loopArcPos N X i + n * N) ∧
        loopArcPos N X j + n1 * N - (loopArcPos N X i + n * N) < 1
  · obtain ⟨n1, h0, h1⟩ := hex
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = loopArcPos N X j + n1 * N - (loopArcPos N X i + n * N) :=
      ⟨_, rfl⟩
    rw [← hd] at h0 h1
    have hdist : dist (loopPos X i) (loopPos X j) = d := by
      refine dist_loopPos_eq_of_forward hN2 X i j h0 h1 (k := n - n1) ?_
      have : (N : ℝ) * X.val j = (N : ℝ) * X.val i + d + ((n : ℝ) - n1) * N := by
        rw [hd]
        simp only [loopArcPos]
        ring
      push_cast
      exact this
    have hji : j ≠ i := by
      rintro rfl
      rw [dist_self] at hdist
      linarith
    have hd3 : dist (loopPos X i) (loopPos X j) ≤ 3 := by rw [hdist]; linarith
    rw [ite_eq_left ⟨hji, hd3⟩, hdist]
    calc _ ≤ ∑' n' : ℤ, if n' = n1 then
            ENNReal.ofReal (((s + 1) * (s + 2))⁻¹) * ENNReal.ofReal (d ^ (-s)) else 0 := by
          refine ENNReal.tsum_le_tsum fun n' => ?_
          refine (hbound n').trans ?_
          by_cases hn' : n' = n1
          · rw [ite_eq_left hn']
            have he : loopArcPos N X j + n' * N - (loopArcPos N X i + n * N) = d := by
              rw [hn', hd]
            rw [he, ite_eq_left ⟨⟨hn1, hn2⟩, h0, h1⟩, div_eq_inv_mul,
              ENNReal.ofReal_mul (by positivity)]
          · rw [ite_eq_right hn', ite_eq_right]
            rintro ⟨_, h2, h3⟩
            refine hn' (lift_eq_of_mem_window (c := loopArcPos N X i + n * N)
              (x := loopArcPos N X j) hN2 ?_ ?_ ?_ ?_).symm
            · linarith
            · linarith
            · linarith
            · linarith
      _ = _ := tsum_ite_eq n1 _
  · refine le_trans (ENNReal.tsum_le_tsum (g := fun _ => 0) fun n' => ?_) ?_
    · refine (hbound n').trans ?_
      rw [ite_eq_right]
      rintro ⟨_, h2, h3⟩
      exact hex ⟨n', h2, h3⟩
    · rw [tsum_zero]
      exact zero_le

/-- The sum over the pairs `(j, n')` for the lifts `n` of the particle `i` is bounded by the
rooted energy of `i`, and vanishes unless `i` lies in the arc `(m - 1, m + 1)`. -/
theorem tsum_sum_pairIntegrand_le {s : ℝ} (hs0 : 0 < s) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (X : Configuration N) (m : ℝ) (i : Fin (N : ℕ)) :
    ∑' n : ℤ, ∑ j : Fin (N : ℕ), ∑' n' : ℤ, ∫⁻ t in Ioc m (m + 1), ∫⁻ u, ∫⁻ v,
        pairIntegrand s (loopArcPos N X i + n * N) (loopArcPos N X j + n' * N) t u v
      ≤ if loopPos X i ∈ microArc N (m - 1) 2 then
          ENNReal.ofReal (((s + 1) * (s + 2))⁻¹) * ENNReal.ofReal (rootedEnergy s X i) else 0 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hin : loopPos X i ∈ microArc N (m - 1) 2
  · rw [ite_eq_left hin]
    obtain ⟨n0, h1, h2⟩ := (loopPos_mem_microArc_iff X i (m - 1) 2).mp hin
    have hw : m - 1 + 2 = m + 1 := by ring
    rw [hw] at h2
    rw [tsum_eq_single n0]
    · calc _ ≤ ∑ j : Fin (N : ℕ), if j ≠ i ∧ dist (loopPos X i) (loopPos X j) ≤ 3 then
              ENNReal.ofReal (((s + 1) * (s + 2))⁻¹) *
                ENNReal.ofReal (dist (loopPos X i) (loopPos X j) ^ (-s)) else 0 :=
            Finset.sum_le_sum fun j _ => tsum_lift_pairIntegrand_le hs0 N hN X m i j n0 h1 h2
        _ = _ := by
            unfold rootedEnergy
            rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.rpow_nonneg dist_nonneg _),
              Finset.mul_sum, Finset.sum_filter]
    · intro n hn
      refine Finset.sum_eq_zero fun j _ => ENNReal.tsum_eq_zero.mpr fun n' => ?_
      refine lintegral_pairIntegrand_eq_zero_of_not_window hs0 _ _ _ ?_
      rintro ⟨h3, h4⟩
      exact hn (lift_eq_of_mem_window (c := m - 1) (x := (N : ℝ) * X.val i) hN2
        (by simp only [loopArcPos] at h3; linarith) (by simp only [loopArcPos] at h4; linarith)
        h1 (by linarith))
  · rw [ite_eq_right hin]
    refine nonpos_iff_eq_zero.mpr (ENNReal.tsum_eq_zero.mpr fun n => ?_)
    refine Finset.sum_eq_zero fun j _ => ENNReal.tsum_eq_zero.mpr fun n' => ?_
    refine lintegral_pairIntegrand_eq_zero_of_not_window hs0 _ _ _ ?_
    rintro ⟨h3, h4⟩
    apply hin
    rw [loopPos_mem_microArc_iff]
    refine ⟨n, ?_, ?_⟩
    · simp only [loopArcPos] at h3; linarith
    · simp only [loopArcPos] at h4; linarith

/-- **Pair sum.** For `N ≥ 2`, `0 < s < 1` and every configuration `X` and cell origin `m`, the
integrals of the pair integrands over all lift pairs are bounded by the window-restricted rooted
energies: `∑_{i,n,j,n'} ∫⁻ pairIntegrand ≤ (K) ∑_{i : z_i ∈ (m-1, m+1)} E_i` with
`K = 1/((s+1)(s+2))`. -/
theorem sum_pairIntegrand_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (X : Configuration N) (m : ℝ) :
    ∑ i : Fin (N : ℕ), ∑' n : ℤ, ∑ j : Fin (N : ℕ), ∑' n' : ℤ,
        ∫⁻ t in Ioc m (m + 1), ∫⁻ u, ∫⁻ v,
          pairIntegrand s (loopArcPos N X i + n * N) (loopArcPos N X j + n' * N) t u v
      ≤ ENNReal.ofReal (((s + 1) * (s + 2))⁻¹) *
          ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then
            ENNReal.ofReal (rootedEnergy s X i) else 0) := by
  have _ := hs1
  calc _ ≤ ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then
          ENNReal.ofReal (((s + 1) * (s + 2))⁻¹) * ENNReal.ofReal (rootedEnergy s X i) else 0) :=
        Finset.sum_le_sum fun i _ => tsum_sum_pairIntegrand_le hs0 N hN X m i
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hin : loopPos X i ∈ microArc N (m - 1) 2
        · rw [ite_eq_left hin, ite_eq_left hin]
        · rw [ite_eq_right hin, ite_eq_right hin, mul_zero]

end Riesz1

end
end
