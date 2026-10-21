/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonProduct
public import Riesz1.Variance.APrioriComparisonCutoffEnergy
/-!
# Variance and cutoff energy of the comparator

The good-event estimate bounds the cutoff comparator pointwise. Its
variance is bounded by the square of this envelope. A clamped comparator
agrees wherever the cutoff is nonzero and has a uniform polynomial bound,
so the selected-edge cutoff energy estimate applies to it.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace Filter Classical

namespace Riesz1.APrioriComparison

/-- Uniform variance and negligible cutoff energy for both comparator weights. -/
theorem comparator_cutoff_estimates (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam γ ε : ℝ) (hlam : 0 ≤ lam) (hγ : 1 < γ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ),
      ∀ (K : ℝ) (hK : 1 ≤ K), ∀ J : Finset (Fin (n + 1)),
      J ⊆ (window n.succPNat K γ).erase ⟨0, n.succPNat.pos⟩ →
      ∀ w : Fin (n + 1) → ℝ,
        (w = comparisonWeight n.succPNat K P.val.2 lam ε ∨
          w = augmentedComparisonWeight n.succPNat K P.val.2 lam ε) →
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      let f := fun y : AnchoredEuclidean n =>
        ∑ i ∈ J, w i * (((n : ℝ) + 1) * anchorVector (WithLp.ofLp y) i - (i : ℕ))
      let η := fun y : AnchoredEuclidean n => anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y)
      ∃ he : MemLp (fun y => f y • gradient η y) 2 (anchoredMeasureE χ),
        ProbabilityTheory.variance (fun y => η y * f y) (anchoredMeasureE χ) ≤
          C * K ^ ((4 + 2 * γ) * ε) * (K ^ (2 * lam) + K ^ P.val.2) ∧
        anchoredInverseEnergy χ
          (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
          (he.toLp _) ≤ C * K ^ (-10 : ℝ) := by
  obtain ⟨Cg, hCg, hgood⟩ := a_priori_comparison_comparator P.val.2 lam γ
    P.2.2.1 P.2.2.2 hlam hγ ε hε hε1
  obtain ⟨Ce, hCe, hcut⟩ := comparison_cutoff_energy hBE hPL P γ ε hγ hε
    (lam + 4) (2 * Cg) 10 (by linarith) (by positivity) (by norm_num)
  refine ⟨2 * Cg ^ 2 + Ce, by positivity, fun n hn θ hθ K hK J hJ w hw => ?_⟩
  have hK0 : 0 < K := by linarith
  let χ := nearestTiltedPairs P n.succPNat hθ K γ ε hK0
  have hc := hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P)
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let f := fun y : AnchoredEuclidean n =>
    ∑ i ∈ J, w i * (((n : ℝ) + 1) * anchorVector (WithLp.ofLp y) i - (i : ℕ))
  let η := fun y : AnchoredEuclidean n => anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y)
  let B := Cg * K ^ (3 * ε) * (K ^ lam + K ^ (P.val.2 / 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsupp : ∀ᵐ y ∂anchoredMeasureE χ, η y ≠ 0 → |f y| ≤ B := by
    apply comparator_bound_on_cutoff_support χ hK0 f
    intro X hX
    have hp := hgood n.succPNat K hK J hJ X hX
    dsimp only [f]
    change |∑ i ∈ J, w i * (((n : ℝ) + 1) * anchorVector (anchorMap n.succPNat X) i - (i : ℕ))| ≤ B
    rw [anchorVector_anchorMap]
    rcases hw with rfl | rfl
    · simpa only [linearComparator, Nat.succPNat_coe, Nat.cast_succ, B] using hp.1
    · simpa only [augmentedLinearComparator, Nat.succPNat_coe, Nat.cast_succ, B] using hp.2
  have hηf := cutoff_comparator_bound χ hB f hsupp
  have hmem := cutoff_comparator_h1 χ hc hn P.val.2 K γ ε hK hε.le f (comparator_smooth n J w)
  have hvar : ProbabilityTheory.variance (fun y => η y * f y) (anchoredMeasureE χ) ≤ B ^ 2 := by
    apply (ProbabilityTheory.variance_le_expectation_sq hmem.1.aestronglyMeasurable).trans
    calc _ ≤ ∫ _ : AnchoredEuclidean n, B ^ 2 ∂anchoredMeasureE χ := by
          apply integral_mono_ae (hmem.1.integrable_sq) (integrable_const _)
          filter_upwards [hηf] with y hy
          change (η y * f y) ^ 2 ≤ B ^ 2
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (η y * f y)) hB).mpr hy
      _ = B ^ 2 := by simp only [integral_const, probReal_univ, one_smul]
  have hpoly : B ≤ 2 * Cg * K ^ (lam + 4) := by
    have h1 : K ^ lam ≤ K ^ (lam + 1) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
    have h2 : K ^ (P.val.2 / 2) ≤ K ^ (lam + 1) :=
      Real.rpow_le_rpow_of_exponent_le hK (by linarith [P.2.2.2])
    have h3 : K ^ (3 * ε) ≤ K ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hK (by linarith)
    calc B ≤ Cg * K ^ (3 : ℝ) * (K ^ (lam + 1) + K ^ (lam + 1)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left h3 hCg.le) (add_le_add h1 h2)
            (by positivity) (by positivity)
      _ = 2 * Cg * (K ^ (3 : ℝ) * K ^ (lam + 1)) := by ring
      _ = 2 * Cg * K ^ (lam + 4) := by
          rw [← Real.rpow_add hK0, show (3 : ℝ) + (lam + 1) = lam + 4 by ring]
  let T := fun z : Fin n → ℝ => max (-B) (min B (f (WithLp.toLp 2 z)))
  have hTm : Measurable T := by
    exact measurable_const.max (measurable_const.min
      ((comparator_smooth n J w).continuous.measurable.comp (PiLp.continuous_toLp 2 _).measurable))
  have hT (z : Fin n → ℝ) : |T z| ≤ 2 * Cg * K ^ (lam + 4) := by
    apply le_trans _ hpoly
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  obtain ⟨heT, heE⟩ := hcut n hn θ hθ K hK T hTm (fun z _ => hT z)
  have heq := clamped_comparator_cutoff_field χ hn P.val.2 K γ ε hK
    (by linarith) P.2.2.1.le hε.le f hsupp
  have he : MemLp (fun y => f y • gradient η y) 2 (anchoredMeasureE χ) := heT.ae_eq heq
  have heLp : he.toLp _ = heT.toLp _ := by
    apply Lp.ext
    filter_upwards [he.coeFn_toLp, heT.coeFn_toLp, heq] with y hy hz heq
    rw [hy, hz, heq]
  refine ⟨he, ?_, ?_⟩
  · have hsum : (K ^ lam + K ^ (P.val.2 / 2)) ^ 2 ≤
        2 * (K ^ (2 * lam) + K ^ P.val.2) := by
      have h1 : (K ^ lam) ^ 2 = K ^ (2 * lam) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; congr 1; ring
      have h2 : (K ^ (P.val.2 / 2)) ^ 2 = K ^ P.val.2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; congr 1; ring
      nlinarith [sq_nonneg (K ^ lam - K ^ (P.val.2 / 2))]
    have hpow : (K ^ (3 * ε)) ^ 2 = K ^ (6 * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; congr 1; ring
    calc _ ≤ B ^ 2 := hvar
      _ ≤ (2 * Cg ^ 2) * K ^ (6 * ε) * (K ^ (2 * lam) + K ^ P.val.2) := by
          dsimp only [B]
          rw [mul_pow, mul_pow, hpow]
          nlinarith only [mul_le_mul_of_nonneg_left hsum (show 0 ≤ Cg ^ 2 * K ^ (6 * ε) by positivity)]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul (by linarith [sq_nonneg Cg])
            (Real.rpow_le_rpow_of_exponent_le hK (by nlinarith)) (by positivity) (by positivity)
  · rw [heLp]
    exact heE.trans (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg Cg]) (by positivity))

end Riesz1.APrioriComparison

end
