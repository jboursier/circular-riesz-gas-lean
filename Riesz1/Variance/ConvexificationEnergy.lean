/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.ConvexificationEnergyBound
public import Riesz1.Variance.ConvexificationVariance

/-!
# Complete convexification and variance transfer

All five claims of Lemma 5.2, with common
constants chosen before the cutoff, particle number, scale and fields.
The inverse energy uses the exact tilted pair datum. Its law identification
is `nearestTiltedPairs_anchoredMeasureE`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Riesz1

/-- **Lemma 5.2, all five claims.** The formulation
allows every `K ≥ 1`, and therefore every mesoscopic scale `K = Nℓ` in
the paper. The only external input, the Prékopa–Leindler inequality
`External.PrekopaLeindler`, is passed explicitly.
-/
theorem a_priori_convexity_complete (hPL : External.PrekopaLeindler) (P : Parameters)
    (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) :
    ∃ c C K₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (hn : 1 ≤ n)
      (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (K : ℝ) (hK : 1 ≤ K),
      totalVariation (gibbsMeasure P n.succPNat) (nearestLaw P θ n.succPNat K γ ε) ≤
        C * Real.exp (-c * K ^ ε) ∧
      (K₀ ≤ K → ∀ᵐ X ∂gibbsMeasure P n.succPNat,
        (nearestLaw P θ n.succPNat K γ ε).rnDeriv (gibbsMeasure P n.succPNat) X ≤ 2) ∧
      (∀ y ∈ anchoredDomain n, ∀ U : Fin n → ℝ,
        c * K ^ (-(((parametersExponent P).val + 2) * ε)) *
          ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
            ((n : ℝ) + 1) ^ 2 * (edgeForm n e U) ^ 2 ≤
          fderiv ℝ (fderiv ℝ (anchoredPotential P.val.1 P.2.1
            (parametersExponent P) θ n K γ ε)) y U U) ∧
      (let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
       let μ := anchoredMeasureE χ
       ∀ (v : Lp (AnchoredEuclidean n) 2 μ)
         (a : AnchoredEuclidean n → Fin (n.succPNat : ℕ) → ℝ),
         (∀ e, MemLp (fun y => a y e) 2 μ) →
         (∀ᵐ y ∂μ, ∀ U : Fin n → ℝ, dotProd (WithLp.ofLp (v y)) U =
           ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
             a y e * (((n : ℝ) + 1) * edgeForm n e U)) →
         anchoredInverseEnergy χ
           (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P)) v ≤
           C * K ^ (((parametersExponent P).val + 2) * ε) *
             ∫ y, (∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ), a y e ^ 2) ∂μ) ∧
      (∀ (M D : ℝ), 0 ≤ M →
        (∀ T : Configuration n.succPNat → ℝ, Measurable T → (∀ X, |T X| ≤ M * K ^ D) →
          |variance T (gibbsMeasure P n.succPNat) - variance T (nearestLaw P θ n.succPNat K γ ε)| ≤
            C * M ^ 2 * K ^ (2 * D) * Real.exp (-c * K ^ ε)) ∧
        (∀ T : (Fin n → ℝ) → ℝ, Measurable T → (∀ y, |T y| ≤ M * K ^ D) →
          |variance T ((gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)) -
              variance T (nearestAnchoredLaw P θ n.succPNat K γ ε)| ≤
            C * M ^ 2 * K ^ (2 * D) * Real.exp (-c * K ^ ε))) := by
  have hγ0 : 0 ≤ γ := by linarith
  obtain ⟨⟨ct, Ct, hct, hCt, ht⟩, K₀, hden⟩ := a_priori_convexity hPL hγ0 hε
  obtain ⟨ch, hch, hh⟩ := anchoredPotential_hessian_lower P.val.1 P.2.1 (parametersExponent P)
  obtain ⟨Ce, hCe, he⟩ := nearestAnchored_inverse_energy P
  obtain ⟨cv, Cv, hcv, hCv, hv⟩ := variance_transfer hPL hγ0 hε
  let c := min ct (min ch cv)
  let C := Ct + Ce + Cv
  have hc : 0 < c := lt_min hct (lt_min hch hcv)
  have hC : 0 < C := by dsimp [C]; linarith
  have hct' : c ≤ ct := min_le_left _ _
  have hch' : c ≤ ch := (min_le_right _ _).trans (min_le_left _ _)
  have hcv' : c ≤ cv := (min_le_right _ _).trans (min_le_right _ _)
  have hCt' : Ct ≤ C := by dsimp [C]; linarith
  have hCe' : Ce ≤ C := by dsimp [C]; linarith
  have hCv' : Cv ≤ C := by dsimp [C]; linarith
  refine ⟨c, C, K₀, hc, hC, fun n hn θ hθ K hK => ?_⟩
  have hN : 2 ≤ (n.succPNat : ℕ) := by simpa using hn
  have hKe : 0 ≤ K ^ ε := Real.rpow_nonneg (by linarith) _
  have hexpt : Real.exp (-ct * K ^ ε) ≤ Real.exp (-c * K ^ ε) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hct') hKe)
  have hexpv : Real.exp (-cv * K ^ ε) ≤ Real.exp (-c * K ^ ε) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hcv') hKe)
  refine ⟨(ht P θ hθ n.succPNat hN K hK).trans
    (mul_le_mul hCt' hexpt (Real.exp_pos _).le hC.le),
    fun hK₀ => hden P θ hθ n.succPNat hN K hK₀ hK, ?_, ?_, ?_⟩
  · intro y hy U
    apply le_trans _ (hh θ hθ n hn K γ ε hK hε.le y hy U)
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hch' (Real.rpow_nonneg (by linarith) _))
    exact Finset.sum_nonneg fun e _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · dsimp only
    intro v a ha hrep
    apply (he n hn θ hθ K γ ε hK hε.le v a ha hrep).trans
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCe' (Real.rpow_nonneg (by linarith) _))
    exact integral_nonneg fun y => Finset.sum_nonneg fun e _ => sq_nonneg _
  · intro M D hM
    obtain ⟨hvf, hva⟩ := hv P θ hθ n.succPNat hN K M D hK hM
    have hfactor : Cv * M ^ 2 * K ^ (2 * D) * Real.exp (-cv * K ^ ε) ≤
        C * M ^ 2 * K ^ (2 * D) * Real.exp (-c * K ^ ε) := by
      apply mul_le_mul _ hexpv (Real.exp_pos _).le (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCv' (sq_nonneg _))
        (Real.rpow_nonneg (by linarith) _)
    exact ⟨fun T hT hTb => (hvf T hT hTb).trans hfactor,
      fun T hT hTb => (hva T hT hTb).trans hfactor⟩

end Riesz1

end
