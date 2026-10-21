/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriUnanchoredBound

/-!
# Normalization and the factor in the unanchored a priori bound

Restores the additive constant of the profile and the factor `M²`, including
`M = 0`, in the second assertion of Lemma 5.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset

namespace Riesz1.Internal

/-- The second bound of Lemma 5.2, for `N ≥ 2`, without normalizing
the test function and with the full factor `M²`. The only hypotheses besides the data are
the Bakry–Émery criterion `hBE` and the Prékopa–Leindler inequality `hPL`. -/
theorem a_priori_unanchored_scaled
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε : ℝ)
    (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n : ℝ) + 1) * ℓ →
      ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ,
      ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ M * cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
      ∃ hF : Integrable (fun X : Configuration n.succPNat =>
          ∑ i, f (X.val i / ℓ)) (gibbsMeasure P n.succPNat),
        Riesz1.variance (gibbsMeasure P n.succPNat) (fun X =>
          ∑ i, f (X.val i / ℓ)) hF ≤
          ENNReal.ofReal (C * M ^ 2 * (((n : ℝ) + 1) * ℓ) ^ (ε + max (2 * lam) P.val.2)) := by
  obtain ⟨C, hC, hb⟩ := a_priori_unanchored_normalized hBE hPL P lam ε hlam hε
  refine ⟨C, hC, fun n hn ℓ hℓ hℓ1 hK M hM f hf hper hder => ?_⟩
  let μ := gibbsMeasure P n.succPNat
  have hprob : IsProbabilityMeasure μ := isProbabilityMeasure_gibbsMeasure P n.succPNat
  have hx (j : Fin (n.succPNat : ℕ)) :
      Measurable (fun X : Configuration n.succPNat => X.val j) :=
    (measurable_pi_apply j).comp measurable_subtype_coe
  by_cases hMz : M = 0
  · have hsup (t : ℝ) : |f t - f (1 / ℓ / 2)| ≤ 0 := by
      have h := abs_sub_antipode_le_kernelSup_mul (s := P.val.2) (lam := lam) (ε := ε)
        (by linarith [P.2.2.2]) hK hlam hε (by positivity) hM hf hper hder t
      simpa only [hMz, zero_mul] using h
    obtain ⟨hF, hvar⟩ := sum_variance_le_of_centered_bound μ n.succPNat f hf.continuous.measurable
      (fun i X => X.val i / ℓ)
      (fun i => (hx i).div_const ℓ)
      (f (1 / ℓ / 2)) 0 le_rfl hsup
    refine ⟨hF, ?_⟩
    simpa only [hMz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul] using hvar
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMz)
  let a := f (1 / ℓ / 2)
  let g := fun u : ℝ => (f u - a) / M
  have hg : ContDiff ℝ 1 g := (hf.sub contDiff_const).div_const M
  have hgper : Function.Periodic g (1 / ℓ) := by
    intro u
    dsimp [g]
    rw [hper u]
  have hgzero : g (1 / ℓ / 2) = 0 := by simp only [g, a, sub_self, zero_div]
  have hgder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv g u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u| := by
    intro u hu
    simp only [g, deriv_div_const, deriv_sub_const, abs_div, abs_of_pos hMpos]
    exact (div_le_iff₀ hMpos).mpr (by simpa only [mul_comm] using hder u hu)
  obtain ⟨hGi, hG, hGb⟩ := hb n hn ℓ hℓ hℓ1 hK g hg hgper hgzero hgder
  let G := fun X : Configuration n.succPNat =>
    ∑ i, g (X.val i / ℓ)
  let F := fun X : Configuration n.succPNat =>
    ∑ i, f (X.val i / ℓ)
  let b := ((n : ℝ) + 1) * a
  have heq : F = fun X => M * G X + b := by
    funext X
    dsimp only [F, G, g, b]
    rw [Finset.mul_sum]
    have hcancel (u : ℝ) : M * ((f u - a) / M) = f u - a := by field_simp
    simp_rw [hcancel]
    rw [Finset.sum_sub_distrib]
    have hcard : (Finset.univ : Finset (Fin (n.succPNat : ℕ))).card = n + 1 := by
      rw [Finset.card_univ, Fintype.card_fin]
      rfl
    simp only [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hF : MemLp F 2 μ := by
    rw [heq]
    exact (hG.const_mul M).add (memLp_const b)
  refine ⟨hF.integrable one_le_two, ?_⟩
  have hGReal : ProbabilityTheory.variance G μ ≤
      C * (((n : ℝ) + 1) * ℓ) ^ (ε + max (2 * lam) P.val.2) := by
    rw [Riesz1.variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
      ← ProbabilityTheory.ofReal_variance hG] at hGb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hGb
  change Riesz1.variance μ F _ ≤ _
  rw [Riesz1.variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
    ← ProbabilityTheory.ofReal_variance hF, heq,
    ProbabilityTheory.variance_add_const (hG.const_mul M).aestronglyMeasurable b,
    ProbabilityTheory.variance_const_mul]
  apply ENNReal.ofReal_le_ofReal
  have hm := mul_le_mul_of_nonneg_left hGReal (sq_nonneg M)
  nlinarith only [hm]

/-- The unanchored assertion of Lemma 5.2 at the original center and
radius, for every particle number, including `N = 1`, and every `M ≥ 0`.
The constant has exactly the dependence and quantifier order of Lemma 5.2. -/
theorem a_priori_unanchored
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε : ℝ)
    (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ,
      ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ M * cutoffMajorant P.val.2 lam ((N : ℝ) * ℓ) |u|) →
      ∃ hF : Integrable (fun X : Configuration N =>
          ∑ i, f (X.val i / ℓ)) (gibbsMeasure P N),
        Riesz1.variance (gibbsMeasure P N) (fun X =>
          ∑ i, f (X.val i / ℓ)) hF ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2)) := by
  obtain ⟨Cg, hCg, hg⟩ := a_priori_unanchored_scaled hBE hPL P lam ε hlam hε
  obtain ⟨Cs, hCs, hs⟩ := a_priori_small_particles P lam ε hlam hε
  refine ⟨Cg + Cs, add_pos hCg hCs, fun N ℓ hℓ hℓ1 hK M hM f hf hper hder => ?_⟩
  by_cases hN : (N : ℕ) ≤ 2
  · obtain ⟨hF, hb⟩ := (hs N hN ℓ hℓ hℓ1 hK M hM f hf hper hder).2
    refine ⟨hF, hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith : 0 ≤ (N : ℝ) * ℓ) _)
    exact mul_le_mul_of_nonneg_right (by linarith : Cs ≤ Cg + Cs) (sq_nonneg M)
  · let n := (N : ℕ) - 1
    have he : N = n.succPNat := by
      apply Subtype.ext
      change (N : ℕ) = n + 1
      dsimp [n]
      omega
    have hn : 1 ≤ n := by dsimp [n]; omega
    rw [he] at hK hder ⊢
    obtain ⟨hF, hb⟩ := hg n hn ℓ hℓ hℓ1
      (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hK) M hM f hf hper
      (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hder)
    refine ⟨hF, hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    simp only [Nat.succPNat_coe, Nat.cast_succ]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (mul_nonneg (by positivity) hℓ.le) _)
    exact mul_le_mul_of_nonneg_right (by linarith : Cg ≤ Cg + Cs) (sq_nonneg M)

end Riesz1.Internal

end
