/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonLp
public import Riesz1.Variance.APrioriCutoffProbability
public import Riesz1.Variance.ConvexificationEnergyLaw
public import Riesz1.ToMathlib.Moments.LpBounds

/-!
# Transfer of comparator moments to the actual tilted law

The forcing normalizer has a positive lower bound uniform in `N` and
the scale. Thus the Gibbs second-moment bound for each affine comparator
transfers to the Euclidean anchored law used by the actual inverse.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace Riesz1.APrioriComparison

/-- The anchored vector of a configuration is its ordered lift shifted
by the first particle, including at the pinned coordinate. -/
theorem anchorVector_anchorMap (n : ℕ) (X : Configuration n.succPNat) :
    anchorVector (anchorMap n.succPNat X) =
      fun i => X.val i - X.val ⟨0, n.succPNat.pos⟩ := by
  have he := anchoredLift_eq_anchorVector n (anchorMap n.succPNat X)
  exact he.symm.trans (anchoredLift_anchorMap X)

/-- Transfer any nonnegative integral from the configuration Gibbs law
to the actual Euclidean anchored tilt. -/
theorem lintegral_tilt_le {n : ℕ} (hn : 1 ≤ n) (P : Parameters)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {K γ ε z : ℝ} (hK : 0 < K) (hz : 0 < z)
    (hZ : z ≤ forcedNormalizer P n.succPNat (nearestForcing θ n.succPNat K γ ε))
    (F : (Fin (n.succPNat : ℕ) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F (anchorVector (WithLp.ofLp y))
        ∂anchoredMeasureE (nearestTiltedPairs P n.succPNat hθ K γ ε hK) ≤
      ENNReal.ofReal z⁻¹ * ∫⁻ X : Configuration n.succPNat,
        F (fun i => X.val i - X.val ⟨0, n.succPNat.pos⟩) ∂gibbsMeasure P n.succPNat := by
  have hm : Measurable (anchorVector : (Fin n → ℝ) → (Fin (n.succPNat : ℕ) → ℝ)) := by
    apply measurable_pi_iff.mpr
    intro i
    induction i using Fin.cases with
    | zero => exact measurable_const
    | succ i => exact measurable_pi_apply i
  rw [nearestTiltedPairs_anchoredMeasureE P hn hθ K γ ε hK]
  erw [lintegral_map ((hF.comp hm).comp (PiLp.continuous_ofLp 2 _).measurable)
      (PiLp.continuous_toLp 2 _).measurable]
  change (∫⁻ y, F (anchorVector y) ∂(nearestLaw P θ n.succPNat K γ ε).map
    (anchorMap n.succPNat)) ≤ _
  erw [lintegral_map (hF.comp hm) (measurable_anchorMap _)]
  have hdom := Internal.nearestLaw_le_of_normalizer_lower P hθ hK hz hZ
  calc _ ≤ ∫⁻ X, F (anchorVector (anchorMap n.succPNat X))
        ∂(ENNReal.ofReal z⁻¹ • gibbsMeasure P n.succPNat) := lintegral_mono' hdom le_rfl
    _ = _ := by
      rw [lintegral_smul_measure]
      congr 1
      apply lintegral_congr
      intro X
      exact congrArg F (anchorVector_anchorMap n X)

/-- Both second moments under the actual tilted anchored law. -/
theorem comparator_tilted_secondMoment (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam γ ε : ℝ) (hlam : 0 ≤ lam) (hγ : 1 < γ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ),
      ∀ (K : ℝ) (hK : 1 ≤ K), ∀ J : Finset (Fin (n.succPNat : ℕ)),
      J ⊆ (window n.succPNat K γ).erase ⟨0, n.succPNat.pos⟩ →
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      (∫⁻ y, ENNReal.ofReal (linearComparator n.succPNat K P.val.2 lam ε J
          (anchorVector (WithLp.ofLp y)) ^ 2) ∂anchoredMeasureE χ ≤
        ENNReal.ofReal (C * K ^ ((4 + 2 * γ) * ε) * (K ^ (2 * lam) + K ^ P.val.2))) ∧
      (∫⁻ y, ENNReal.ofReal (augmentedLinearComparator n.succPNat K P.val.2 lam ε J
          (anchorVector (WithLp.ofLp y)) ^ 2) ∂anchoredMeasureE χ ≤
        ENNReal.ofReal (C * K ^ ((4 + 2 * γ) * ε) * (K ^ (2 * lam) + K ^ P.val.2))) := by
  obtain ⟨CL, hCL, hLp⟩ := comparator_L2 hBE hPL P lam γ ε hlam hγ hε hε1
  obtain ⟨z, hz, hZ⟩ := nearestNormalizer_uniform hPL P γ ε (by linarith) hε
  refine ⟨2 * z⁻¹ * CL ^ 2, by positivity, fun n hn θ hθ K hK J hJ => ?_⟩
  have hK0 : 0 < K := by linarith
  have hN : 2 ≤ (n.succPNat : ℕ) := by simpa using hn
  have hp := hLp n.succPNat hN K hK J hJ
  have hbound (G : (Fin (n.succPNat : ℕ) → ℝ) → ℝ) (hG : Measurable G)
      (hL : eLpNorm (fun X : Configuration n.succPNat =>
        G (fun i => X.val i - X.val ⟨0, n.succPNat.pos⟩)) 2 (gibbsMeasure P n.succPNat) ≤
          ENNReal.ofReal (CL * K ^ ((2 + γ) * ε) * (K ^ lam + K ^ (P.val.2 / 2)))) :
      ∫⁻ y, ENNReal.ofReal (G (anchorVector (WithLp.ofLp y)) ^ 2)
          ∂anchoredMeasureE (nearestTiltedPairs P n.succPNat hθ K γ ε hK0) ≤
        ENNReal.ofReal (2 * z⁻¹ * CL ^ 2 * K ^ ((4 + 2 * γ) * ε) *
          (K ^ (2 * lam) + K ^ P.val.2)) := by
    have hmeas : Measurable (fun X : Configuration n.succPNat =>
        G (fun i => X.val i - X.val ⟨0, n.succPNat.pos⟩)) := by
      apply hG.comp
      exact measurable_pi_iff.mpr fun i =>
        ((measurable_pi_apply i).comp measurable_subtype_coe).sub
          ((measurable_pi_apply (⟨0, n.succPNat.pos⟩ : Fin (n.succPNat : ℕ))).comp
            measurable_subtype_coe)
    have hsq := lintegral_pow_le_of_eLpNorm_le hmeas (m := 2) (by norm_num)
      (show 0 ≤ CL * K ^ ((2 + γ) * ε) * (K ^ lam + K ^ (P.val.2 / 2)) by positivity)
      (by simpa using hL)
    simp only [sq_abs] at hsq
    have htr := lintegral_tilt_le hn P hθ hK0 hz (hZ _ hN θ hθ K hK)
      (fun y => ENNReal.ofReal (G y ^ 2)) ((hG.pow_const 2).ennreal_ofReal)
    apply htr.trans
    apply (mul_le_mul_of_nonneg_left hsq zero_le).trans
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hsum : (K ^ lam + K ^ (P.val.2 / 2)) ^ 2 ≤
        2 * (K ^ (2 * lam) + K ^ P.val.2) := by
      have h1 : (K ^ lam) ^ 2 = K ^ (2 * lam) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; congr 1; ring
      have h2 : (K ^ (P.val.2 / 2)) ^ 2 = K ^ P.val.2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; congr 1; ring
      nlinarith [sq_nonneg (K ^ lam - K ^ (P.val.2 / 2))]
    have heq : (K ^ ((2 + γ) * ε)) ^ 2 = K ^ ((4 + 2 * γ) * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; congr 1; ring
    rw [mul_pow, mul_pow, heq]
    nlinarith only [mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ z⁻¹ * (CL ^ 2 * K ^ ((4 + 2 * γ) * ε)) by positivity)]
  constructor
  · apply hbound _ _ hp.1
    unfold linearComparator
    fun_prop
  · apply hbound _ _ hp.2
    unfold augmentedLinearComparator
    fun_prop

end Riesz1.APrioriComparison

end
