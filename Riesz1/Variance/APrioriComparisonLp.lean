/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonMoments

/-!
# Square integrable affine comparators

Rigidity bounds each coordinate error in `L²`. Minkowski and the two
weight sums bound the entire affine comparator, without differentiating
the good-event cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1.APrioriComparison

/-- Extra powers of a label distance are absorbed using the window radius. -/
theorem sum_extra_power_le {N : ℕ+} {K s γ ε δ : ℝ} (hK : 1 ≤ K)
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (hε1 : ε ≤ 1)
    (J : Finset (Fin (N : ℕ))) (hJ : J ⊆ (window N K γ).erase ⟨0, N.pos⟩)
    (w : Fin (N : ℕ) → ℝ) (hw : ∀ i ∈ J, 0 ≤ w i) :
    ∑ i ∈ J, w i * (labelDistToOne N i : ℝ) ^ (s / 2 + δ) ≤
      (4 * K ^ (γ * ε)) * ∑ i ∈ J, w i * (labelDistToOne N i : ℝ) ^ (s / 2) := by
  have hK0 : 0 < K := by linarith
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := mem_erase.mp (hJ hi)
  have hd0 : 0 < (labelDistToOne N i : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (distance_pos hi'.1)
  have hp : (labelDistToOne N i : ℝ) ^ δ ≤ 4 * K ^ (γ * ε) := by
    calc _ ≤ (4 * K ^ γ) ^ δ :=
          Real.rpow_le_rpow hd0.le (labelDist_le_of_mem_window hK hi'.2) hδ
      _ = 4 ^ δ * K ^ (γ * δ) := by rw [Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_mul hK0.le]
      _ ≤ 4 * K ^ (γ * ε) := by
          apply mul_le_mul
          · calc (4 : ℝ) ^ δ ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 4 := Real.rpow_one _
          · exact Real.rpow_le_rpow_of_exponent_le hK (mul_le_mul_of_nonneg_left hδε hγ)
          · positivity
          · norm_num
  rw [Real.rpow_add hd0]
  have h := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (hw i hi) (Real.rpow_nonneg hd0.le (s / 2)))
  nlinarith only [h]

/-- Minkowski for a weighted sum of anchored errors. All analytic
hypotheses occur only in this internal helper. -/
theorem comparator_eLpNorm_le {N : ℕ+} {P : Parameters} {q C : ℝ}
    (J : Finset (Fin (N : ℕ))) (w : Fin (N : ℕ) → ℝ) (hw : ∀ i ∈ J, 0 ≤ w i)
    (hC : 0 ≤ C)
    (herr : ∀ i ∈ J, eLpNorm (fun X : Configuration N =>
      ((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - (i : ℕ)) 2 (gibbsMeasure P N) ≤
        ENNReal.ofReal (C * (labelDistToOne N i : ℝ) ^ q)) :
    eLpNorm (fun X : Configuration N => ∑ i ∈ J, w i *
      (((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - (i : ℕ))) 2 (gibbsMeasure P N) ≤
        ENNReal.ofReal (C * ∑ i ∈ J, w i * (labelDistToOne N i : ℝ) ^ q) := by
  let f : Fin (N : ℕ) → Configuration N → ℝ := fun i X =>
    ((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - (i : ℕ)
  have heq : (fun X => ∑ i ∈ J, w i * f i X) = ∑ i ∈ J, w i • f i := by
    ext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change eLpNorm (fun X => ∑ i ∈ J, w i * f i X) 2 _ ≤ _
  rw [heq]
  calc _ ≤ ∑ i ∈ J, eLpNorm (w i • f i) 2 (gibbsMeasure P N) := eLpNorm_sum_le (by norm_num)
    _ ≤ ∑ i ∈ J, ENNReal.ofReal (C * (w i * (labelDistToOne N i : ℝ) ^ q)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (hw i hi)]
        apply (mul_le_mul_of_nonneg_left (herr i hi) zero_le).trans_eq
        rw [← ENNReal.ofReal_mul (hw i hi)]
        congr 1
        ring
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi =>
          mul_nonneg hC (mul_nonneg (hw i hi) (Real.rpow_nonneg (Nat.cast_nonneg _) _))),
          ← Finset.mul_sum]

/-- Uniform Gibbs `L²` bounds for both affine comparators. -/
theorem comparator_L2 (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam γ ε : ℝ) (hlam : 0 ≤ lam) (hγ : 1 < γ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ K : ℝ, 1 ≤ K →
      ∀ J : Finset (Fin (N : ℕ)), J ⊆ (window N K γ).erase ⟨0, N.pos⟩ →
        (eLpNorm (fun X : Configuration N => linearComparator N K P.val.2 lam ε J
            (fun i => X.val i - X.val ⟨0, N.pos⟩)) 2 (gibbsMeasure P N) ≤
          ENNReal.ofReal (C * K ^ ((2 + γ) * ε) * (K ^ lam + K ^ (P.val.2 / 2)))) ∧
        (eLpNorm (fun X : Configuration N => augmentedLinearComparator N K P.val.2 lam ε J
            (fun i => X.val i - X.val ⟨0, N.pos⟩)) 2 (gibbsMeasure P N) ≤
          ENNReal.ofReal (C * K ^ ((2 + γ) * ε) * (K ^ lam + K ^ (P.val.2 / 2)))) := by
  obtain ⟨δ₀, hδ₀, herr⟩ := anchoredError_moments hBE hPL P
  let δ := min (ε / 2) (min (P.val.2 / 4) (δ₀ / 2))
  have hδ : 0 < δ := by have := P.2.2.1; dsimp [δ]; positivity
  have hδε : δ ≤ ε := (min_le_left _ _).trans (by linarith)
  have hδs : δ < min (P.val.2 / 2) δ₀ := by
    have h1 : δ ≤ P.val.2 / 4 := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : δ ≤ δ₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
    exact lt_min (by linarith [P.2.2.1]) (by linarith)
  obtain ⟨CE, hCE, herr⟩ := herr δ hδ hδs
  obtain ⟨CS, hCS, hsum⟩ := comparison_sums_le P.val.2 lam γ P.2.2.1 P.2.2.2 hlam hγ ε hε hε1
  refine ⟨4 * CE * CS, by positivity, fun N hN K hK J hJ => ?_⟩
  have hK0 : 0 < K := by linarith
  have hJ0 : ∀ i ∈ J, i ≠ ⟨0, N.pos⟩ := fun i hi => (mem_erase.mp (hJ hi)).1
  have hbound (w : Fin (N : ℕ) → ℝ) (hw : ∀ i ∈ J, 0 ≤ w i)
      (hS : ∑ i ∈ J, w i * (labelDistToOne N i : ℝ) ^ (P.val.2 / 2) ≤
        CS * K ^ (2 * ε) * (K ^ lam + K ^ (P.val.2 / 2))) :
      eLpNorm (fun X : Configuration N => ∑ i ∈ J, w i *
        (((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - (i : ℕ))) 2 (gibbsMeasure P N) ≤
          ENNReal.ofReal (4 * CE * CS * K ^ ((2 + γ) * ε) * (K ^ lam + K ^ (P.val.2 / 2))) := by
    apply (comparator_eLpNorm_le J w hw hCE.le (fun i hi => herr N hN i (hJ0 i hi))).trans
    apply ENNReal.ofReal_le_ofReal
    have h := sum_extra_power_le (s := P.val.2) hK (by linarith : 0 ≤ γ)
      hδ.le hδε hε1 J hJ w hw
    have hh := mul_le_mul_of_nonneg_left hS (show 0 ≤ 4 * K ^ (γ * ε) by positivity)
    have heq : CE * ((4 * K ^ (γ * ε)) * (CS * K ^ (2 * ε) * (K ^ lam + K ^ (P.val.2 / 2)))) =
        4 * CE * CS * K ^ ((2 + γ) * ε) * (K ^ lam + K ^ (P.val.2 / 2)) := by
      rw [show (2 + γ) * ε = γ * ε + 2 * ε by ring, Real.rpow_add hK0]
      ring
    exact (mul_le_mul_of_nonneg_left (h.trans hh) hCE.le).trans_eq heq
  exact ⟨hbound _ (fun i _ => comparisonWeight_nonneg hK0.le i) (hsum N K hK J hJ).1,
    hbound _ (fun i _ => augmentedComparisonWeight_nonneg hK0.le i) (hsum N K hK J hJ).2⟩

end Riesz1.APrioriComparison

end
