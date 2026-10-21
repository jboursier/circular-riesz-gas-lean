/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriBoundEnergy
public import Riesz1.Variance.APrioriBoundGradientEnergy
public import Riesz1.Variance.APrioriBoundLocalization
public import Riesz1.Variance.APrioriComparisonAdmissible

/-!
# The localized variance under the convexified law

The product-rule and inverse-energy step in the proof of Lemma 5.2.
The conditional statements in this file are internal helpers: the hypothesis
is actual membership in the Sobolev completion, with the literal
cutoff field. No variance estimate is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace

namespace Riesz1.Internal

/-- The representation and two-field split for actual function representatives.
This includes the first-moment certificate needed by the variance. -/
theorem anchored_product_variance_le {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hPL : External.PrekopaLeindler) (hn : 0 < n)
    {C_N : ℝ} (hadm : HsAdmissible χ C_N)
    {F : AnchoredEuclidean n → ℝ} {v w : AnchoredEuclidean n → AnchoredEuclidean n}
    (hv : MemLp v 2 (anchoredMeasureE χ)) (hw : MemLp w 2 (anchoredMeasureE χ))
    (hH : IsAnchoredH1 χ F (fun y => v y + w y)) :
    ∃ hF : Integrable F (anchoredMeasureE χ),
      Riesz1.variance (anchoredMeasureE χ) F hF ≤ ENNReal.ofReal
        (2 * anchoredInverseEnergy χ hc (hv.toLp v) +
          2 * anchoredInverseEnergy χ hc (hw.toLp w)) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let S : AnchoredSobolev χ := ⟨(hH.1.toLp F, (hv.add hw).toLp (fun y => v y + w y)),
    WeightedSobolev.IsWeightedH1.congr hH hH.1.coeFn_toLp.symm (hv.add hw).coeFn_toLp.symm⟩
  have hg : S.val.2 = hv.toLp v + hw.toLp w := by
    apply Lp.ext
    filter_upwards [(hv.add hw).coeFn_toLp, hv.coeFn_toLp, hw.coeFn_toLp,
      Lp.coeFn_add (hv.toLp v) (hw.toLp w)] with y hsum hv' hw' hadd
    exact hsum.trans ((congrArg₂ (· + ·) hv' hw').symm.trans hadd.symm)
  have hb := anchored_variance_le_split_inverseEnergy χ hc hPL hn hadm S
    (hv.toLp v) (hw.toLp w) hg
  have he : ProbabilityTheory.variance F (anchoredMeasureE χ) =
      ProbabilityTheory.variance S.val.1 (anchoredMeasureE χ) :=
    ProbabilityTheory.variance_congr hH.1.coeFn_toLp.symm
  refine ⟨hH.1.integrable one_le_two, ?_⟩
  rw [Riesz1.variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
    ← ProbabilityTheory.ofReal_variance hH.1, he]
  exact ENNReal.ofReal_le_ofReal hb

/-- The cutoff-gradient term for the normalized localized sum is negligible,
with a constant uniform in the particle number, scale, forcing cutoff and test.
This is the second energy term in the proof of Lemma 5.2. -/
theorem a_priori_localized_cutoff_energy (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (lam γ ε b : ℝ)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) (hε : 0 < ε) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 →
      ∀ hK : 1 ≤ ((n : ℝ) + 1) * ℓ,
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      f (1 / ℓ / 2) = 0 →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
      let K := ((n : ℝ) + 1) * ℓ
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      let F := fun y : Fin n → ℝ =>
        ∑ j ∈ window n.succPNat K γ, f (anchorVector y j / ℓ)
      ∃ hw : MemLp (anchoredCutoffField n P.val.2 K γ ε F) 2 (anchoredMeasureE χ),
        anchoredInverseEnergy χ
          (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
          (hw.toLp (anchoredCutoffField n P.val.2 K γ ε F)) ≤ C * K ^ (-b) := by
  have hM : 0 < 9 * kernelSupConst P.val.2 lam ε := by
    dsimp [kernelSupConst]
    have : 0 < lam + ε := by linarith
    have : 0 < 2 - P.val.2 := by linarith [P.2.2.2]
    positivity
  obtain ⟨C, hC, hc⟩ := a_priori_cutoff_complete hBE hPL P γ ε hγ hε
    (γ + lam + ε) (9 * kernelSupConst P.val.2 lam ε) b (by linarith) hM hb
  refine ⟨C, hC, fun n hn θ hθ ℓ hℓ hℓ1 hK f hf hper hzero hder => ?_⟩
  apply (hc n hn θ hθ ℓ hℓ hℓ1 hK).1
  · apply Finset.measurable_sum
    intro i _
    apply hf.continuous.measurable.comp
    simpa only [anchorCoord_apply] using (anchorCoord n i).continuous.measurable.div_const ℓ
  · intro y _
    exact localizedStatistic_abs_le n hℓ hK (by linarith) (by linarith [P.2.2.2])
      hlam hε hf hper hzero hder y

/-- Under the sole completion-membership obligation, the normalized cutoff
statistic has the required variance rate under the actual tilted law.
Both rate parameters are chosen before the auxiliary exponent. -/
theorem a_priori_localized_tilted_variance (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (lam γ : ℝ)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) :
    ∃ κ ε₀ : ℝ, 0 < κ ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 →
      ∀ hK : 1 ≤ ((n : ℝ) + 1) * ℓ,
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      f (1 / ℓ / 2) = 0 →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
      let K := ((n : ℝ) + 1) * ℓ
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      let F := fun y : Fin n → ℝ =>
        ∑ j ∈ window n.succPNat K γ, f (anchorVector y j / ℓ)
      let η := fun y : AnchoredEuclidean n =>
        anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y)
      let V := fun y : AnchoredEuclidean n => η y • gradient (fun z => F (WithLp.ofLp z)) y
      let W := anchoredCutoffField n P.val.2 K γ ε F
      IsAnchoredH1 χ (fun y => η y * F (WithLp.ofLp y)) (fun y => V y + W y) →
      ∃ hT : Integrable (fun y => η y * F (WithLp.ofLp y)) (anchoredMeasureE χ),
        Riesz1.variance (anchoredMeasureE χ) (fun y => η y * F (WithLp.ofLp y)) hT ≤
          ENNReal.ofReal (C * K ^ (κ * ε) * (K ^ (2 * lam) + K ^ P.val.2)) := by
  obtain ⟨κ, ε₀, hκ, hε₀, hg⟩ :=
    a_priori_localized_gradient_energy hBE hPL P lam γ hlam hγ
  refine ⟨κ, ε₀, hκ, hε₀, fun ε hε hεs => ?_⟩
  obtain ⟨Cg, hCg, hgv⟩ := hg ε hε hεs
  obtain ⟨Cw, hCw, hwv⟩ :=
    a_priori_localized_cutoff_energy hBE hPL P lam γ ε 10 hlam hγ hε (by norm_num)
  refine ⟨2 * Cg + 2 * Cw, by positivity, ?_⟩
  intro n hn θ hθ ℓ hℓ hℓ1 hK f hf hper hzero hder
  dsimp only
  intro hH
  obtain ⟨hv, hvb⟩ := hgv n hn θ hθ ℓ hℓ hK f hf hper hder
  obtain ⟨hw, hwb⟩ := hwv n hn θ hθ ℓ hℓ hℓ1 hK f hf hper hzero hder
  obtain ⟨C_N, hadm⟩ := APrioriComparison.nearestTiltedPairs_admissible P n.succPNat
    (by simpa using hn) hθ (((n : ℝ) + 1) * ℓ) γ ε (by linarith)
  obtain ⟨hT, hb⟩ := anchored_product_variance_le _
    (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
    hPL (by omega) hadm hv hw hH
  refine ⟨hT, hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  let K := ((n : ℝ) + 1) * ℓ
  have hp : 1 ≤ K ^ (κ * ε) := Real.one_le_rpow hK (by positivity)
  have hsum : 1 ≤ K ^ (2 * lam) + K ^ P.val.2 := by
    have h1 := Real.one_le_rpow hK (show 0 ≤ 2 * lam by positivity)
    have h2 := Real.rpow_nonneg (show 0 ≤ K by dsimp [K]; linarith) P.val.2
    linarith
  have hlow : K ^ (-(10 : ℝ)) ≤ K ^ (κ * ε) * (K ^ (2 * lam) + K ^ P.val.2) := by
    apply (Real.rpow_le_one_of_one_le_of_nonpos hK (by norm_num)).trans
    exact one_le_mul_of_one_le_of_one_le hp hsum
  have hwbig := hwb.trans (mul_le_mul_of_nonneg_left hlow hCw.le)
  calc _ ≤ 2 * (Cg * K ^ (κ * ε) * (K ^ (2 * lam) + K ^ P.val.2)) +
        2 * (Cw * (K ^ (κ * ε) * (K ^ (2 * lam) + K ^ P.val.2))) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hvb (by norm_num))
            (mul_le_mul_of_nonneg_left hwbig (by norm_num))
    _ = _ := by ring

end Riesz1.Internal

end
