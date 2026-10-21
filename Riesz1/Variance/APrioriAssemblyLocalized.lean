/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriAssemblyEnergy
public import Riesz1.Variance.APrioriMembershipInput
public import Riesz1.Variance.ConvexificationVariance
public import Riesz1.ToMathlib.Moments.Decay
public import Riesz1.ToMathlib.VarianceTwoErrors

/-!
# Localized Gibbs variance from cutoff-product membership

The variance transfer and removed-statistic steps of Lemma 5.2.
The hypotheses are the Bakry–Émery criterion `External.BakryEmery`, the Prékopa–Leindler
inequality `External.PrekopaLeindler`, and the Sobolev membership proposition
`APrioriMembershipInput`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace

namespace Riesz1.Internal

/-- The rate appearing in the comparison and localized variance is at least one,
including the boundary scale `K = 1`. -/
theorem one_le_a_priori_rate {K κ ε lam s : ℝ} (hK : 1 ≤ K)
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hlam : 0 ≤ lam) :
    1 ≤ K ^ (κ * ε) * (K ^ (2 * lam) + K ^ s) := by
  have hp := Real.one_le_rpow hK (mul_nonneg hκ hε)
  have hi := Real.one_le_rpow hK (show 0 ≤ 2 * lam by positivity)
  have ho := Real.rpow_nonneg (show 0 ≤ K by linarith) s
  exact one_le_mul_of_one_le_of_one_le hp (by linarith)

/-- The localized normalized statistic under the original Gibbs anchored law.
The constants are uniform before `n, ℓ, f`, and the rate exponent is chosen
before the auxiliary `ε`. This closes the variance-transfer and removed-cutoff
steps of Lemma 5.2, conditional only on completion membership. -/
theorem a_priori_localized_variance_of_membership
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (hmem : APrioriMembershipInput) (P : Parameters) (lam γ : ℝ)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) :
    ∃ κ ε₀ : ℝ, 0 < κ ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n : ℝ) + 1) * ℓ →
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      f (1 / ℓ / 2) = 0 →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
      let K := ((n : ℝ) + 1) * ℓ
      let μ := (gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)
      let F := fun y : Fin n → ℝ =>
        ∑ j ∈ window n.succPNat K γ, f (anchorVector y j / ℓ)
      ∃ hF : Integrable F μ, MemLp F 2 μ ∧ Riesz1.variance μ F hF ≤
        ENNReal.ofReal (C * K ^ (κ * ε) * (K ^ (2 * lam) + K ^ P.val.2)) := by
  obtain ⟨κ, ε₀, hκ, hε₀, ht⟩ := a_priori_localized_tilted_variance hBE hPL P lam γ hlam hγ
  refine ⟨κ, ε₀, hκ, hε₀, fun ε hε hεs => ?_⟩
  obtain ⟨Ct, hCt, htv⟩ := ht ε hε hεs
  obtain ⟨Cr, hCr, hrem⟩ := localizedStatistic_removed_L2 hBE hPL P γ lam ε 10
    hγ hlam hε (by norm_num)
  obtain ⟨c, Cv, hc, hCv, htransfer⟩ := variance_transfer hPL (show 0 ≤ γ by linarith) hε
  let M := 9 * kernelSupConst P.val.2 lam ε
  let D := γ + lam + ε
  have hM : 0 < M := by
    dsimp [M, kernelSupConst]
    have : 0 < lam + ε := by linarith
    have : 0 < 2 - P.val.2 := by linarith [P.2.2.2]
    positivity
  obtain ⟨B, hB, hdecay⟩ := rpow_mul_exp_neg_bounded (β := 2 * D) hε hc
  let A := Ct + Cv * M ^ 2 * B
  refine ⟨3 * (Cr ^ 2 + A), by dsimp [A]; positivity, ?_⟩
  intro n hn ℓ hℓ hℓ1 hK f hf hper hzero hder
  dsimp only
  let K := ((n : ℝ) + 1) * ℓ
  let μ : Measure (Fin n → ℝ) := (gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)
  let ν : Measure (Fin n → ℝ) := nearestAnchoredLaw P forcingCutoff n.succPNat K γ ε
  let F := fun y : Fin n → ℝ => ∑ j ∈ window n.succPNat K γ, f (anchorVector y j / ℓ)
  let η := anchoredCutoff n.succPNat P.val.2 K γ ε
  let T := fun y : Fin n → ℝ => η y * F y
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hFm : Measurable F := by
    apply Finset.measurable_sum
    intro i _
    apply hf.continuous.measurable.comp
    simpa only [anchorCoord_apply] using (anchorCoord n i).continuous.measurable.div_const ℓ
  have hηm : Measurable η := measurable_anchoredCutoff _ _ _ _
  have hTm : Measurable T := hηm.mul hFm
  have hsup (y : Fin n → ℝ) : |F y| ≤ M * K ^ D :=
    localizedStatistic_abs_le n hℓ hK (by linarith) (by linarith [P.2.2.2])
      hlam hε hf hper hzero hder y
  have hTsup (y : Fin n → ℝ) : |T y| ≤ M * K ^ D := by
    rw [show T y = η y * F y from rfl, abs_mul,
      abs_of_nonneg (show 0 ≤ η y from anchoredCutoff_nonneg _ _ _ _ _)]
    exact (mul_le_mul_of_nonneg_right (anchoredCutoff_le_one _ _ _ _ _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using hsup y)
  have hprob : IsProbabilityMeasure (gibbsMeasure P n.succPNat) :=
    isProbabilityMeasure_gibbsMeasure P n.succPNat
  have hprobμ : IsProbabilityMeasure μ := inferInstanceAs
    (IsProbabilityMeasure ((gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)))
  have hF : MemLp F 2 μ := MemLp.of_bound hFm.aestronglyMeasurable _
    (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hsup y)
  have hT : MemLp T 2 μ := MemLp.of_bound hTm.aestronglyMeasurable _
    (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hTsup y)
  have hH := hmem P n hn forcingCutoff isForcingCutoff_forcingCutoff ℓ hℓ hK γ ε hγ hε f hf
  obtain ⟨hTE, htilt⟩ := htv n hn forcingCutoff isForcingCutoff_forcingCutoff ℓ hℓ hℓ1 hK
    f hf hper hzero hder hH
  let Q := K ^ (κ * ε) * (K ^ (2 * lam) + K ^ P.val.2)
  have hQ : 1 ≤ Q := one_le_a_priori_rate hK hκ.le hε.le hlam
  have htiltReal : ProbabilityTheory.variance T ν ≤ Ct * Q := by
    have := isProbabilityMeasure_anchoredMeasureE
      (nearestTiltedPairs P n.succPNat isForcingCutoff_forcingCutoff K γ ε hK0)
      (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
    rw [Riesz1.variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
      ← ProbabilityTheory.ofReal_variance hH.1] at htilt
    rw [nearestTiltedPairs_anchoredMeasureE P hn isForcingCutoff_forcingCutoff _ γ ε hK0] at htilt
    have hmap := ProbabilityTheory.variance_map (μ := ν) (X := T ∘ WithLp.ofLp)
      ((hTm.comp (PiLp.continuous_ofLp 2 _).measurable).aemeasurable)
      (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.aemeasurable
    have hmap' : ProbabilityTheory.variance (T ∘ WithLp.ofLp)
        (ν.map (WithLp.toLp 2)) = ProbabilityTheory.variance T ν := by
      convert hmap using 1
      congr 1
    change ENNReal.ofReal (ProbabilityTheory.variance (T ∘ WithLp.ofLp)
      (ν.map (WithLp.toLp 2))) ≤ ENNReal.ofReal (Ct * K ^ (κ * ε) *
        (K ^ (2 * lam) + K ^ P.val.2)) at htilt
    rw [hmap'] at htilt
    simpa only [Q, mul_assoc] using
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htilt
  have htrans := (htransfer P forcingCutoff isForcingCutoff_forcingCutoff n.succPNat
    (by simpa using hn) K M D hK hM.le).2 T hTm hTsup
  change |ProbabilityTheory.variance T μ - ProbabilityTheory.variance T ν| ≤ _ at htrans
  have hGvar : ProbabilityTheory.variance T μ ≤ A * Q := by
    have hdec := hdecay K hK
    have htErr : Cv * M ^ 2 * K ^ (2 * D) * Real.exp (-c * K ^ ε) ≤ Cv * M ^ 2 * B := by
      calc _ = (Cv * M ^ 2) * (K ^ (2 * D) * Real.exp (-c * K ^ ε)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hdec (by positivity)
    have herrQ : Cv * M ^ 2 * B ≤ Cv * M ^ 2 * B * Q :=
      le_mul_of_one_le_right (by positivity) hQ
    have hreal : ProbabilityTheory.variance T μ ≤ Ct * Q + Cv * M ^ 2 * B * Q := by
      have := le_abs_self (ProbabilityTheory.variance T μ - ProbabilityTheory.variance T ν)
      linarith
    dsimp [A]
    nlinarith only [hreal]
  have hGext : Riesz1.variance μ T (hT.integrable one_le_two) ≤ ENNReal.ofReal (A * Q) := by
    rw [Riesz1.variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
      ← ProbabilityTheory.ofReal_variance hT]
    exact ENNReal.ofReal_le_ofReal hGvar
  have hr := hrem n hn ℓ hℓ hℓ1 hK f hf hper hzero hder
  have herr : eLpNorm (fun y => F y - T y - 0) 2 μ ≤ ENNReal.ofReal Cr := by
    have he : (fun y => F y - T y - 0) = (fun y => (1 - η y) * F y) := by
      funext y
      dsimp [T]
      ring
    rw [he]
    apply hr.trans (ENNReal.ofReal_le_ofReal _)
    exact mul_le_of_le_one_right hCr.le (Real.rpow_le_one_of_one_le_of_nonpos hK (by norm_num))
  have hv := variance_le_two_errors μ hF hT hT 0
  have hz : eLpNorm (fun y => T y - T y) 2 μ = 0 := by simp
  rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hv
  refine ⟨hF.integrable one_le_two, hF, hv.trans ?_⟩
  calc _ ≤ 3 * (ENNReal.ofReal Cr ^ 2 + ENNReal.ofReal (A * Q)) := by
        gcongr
    _ = ENNReal.ofReal (3 * (Cr ^ 2 + A * Q)) := by
        rw [← ENNReal.ofReal_pow hCr.le, ← ENNReal.ofReal_add (sq_nonneg _) (by dsimp [A]; positivity),
          ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ ≤ ENNReal.ofReal (3 * (Cr ^ 2 + A) * K ^ (κ * ε) * (K ^ (2 * lam) + K ^ P.val.2)) := by
        apply ENNReal.ofReal_le_ofReal
        have hCrQ := le_mul_of_one_le_right (sq_nonneg Cr) hQ
        dsimp only [Q] at hCrQ ⊢
        nlinarith only [hCrQ]

end Riesz1.Internal

end
