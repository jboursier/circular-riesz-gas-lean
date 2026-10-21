/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringRegularity
public import Riesz1.ToMathlib.SizeBiasedVariance
public import Riesz1.Rigidity.RigidityTheorem

/-!
# Removing the size weight from the localized loop variance

The second assertion of the anchoring part of Lemma 5.8, including
finite second moments for both laws. The rigidity input is supplied through
the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler`. Quadrature is not needed for this
assertion. Constants precede the particle number, scale, and test function.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The size-weighted variance bound of the anchoring part of Lemma 5.8.
This stronger parameter range needs only `γ > 1`, and no quadrature input.
The existential certificates conclude square integrability before either
extended variance is used. -/
theorem loopAnchoring_sizeWeighted_variance (β s α γ ε : ℝ)
    (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 1 < γ)
    (hε : 0 < ε) (hε1 : ε < min (1 / 8) ((1 - s / 2) / 8))
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ C₀ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
      let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
      letI := isProbabilityMeasure_anchoredLaw P (n + 1)
      let F := fun y => loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (anchorVector y)
      ∃ hF : MemLp F 2 (anchoredLaw P (n + 1)),
      ∃ hFw : MemLp F 2 (loopSizeBiasedLaw P n),
        variance (loopSizeBiasedLaw P n) F (hFw.integrable one_le_two) ≤
          ENNReal.ofReal ((((n + 1).succPNat : ℝ) * ℓ) ^ ε) *
            variance (anchoredLaw P (n + 1)) F (hF.integrable one_le_two) +
              ENNReal.ofReal (C * C₀ ^ 2 *
                (((n + 1).succPNat : ℝ) * ℓ) ^ (-10 : ℝ)) := by
  have hεs : ε ≤ 1 - s / 2 := by
    have hh := hε1.trans_le (min_le_right _ _)
    linarith
  obtain ⟨Cf, hCf, hf⟩ := loopCutoffF_explicit_bound hs hs1 hα hα2 hγ hε hεs
    hχ hχc hχs hχ1 hχ01
  let B := (1 - s + α) + 2 * γ + ε * (s + 1)
  have hB : 0 < B := by
    dsimp [B]
    have : 0 < ε * (s + 1) := mul_pos hε (by linarith)
    linarith
  have hRig := rigidityConclusion_of_externals hBE hPL β s hβ hs hs1
  obtain ⟨Cp, hCp, hp⟩ := loopSizeBiased_cutoff_probability_of_rigidity
    β s hβ hs hs1 hRig hPL γ ε hγ hε hε1 (B₀ := 2 * B + 10) (by positivity)
  refine ⟨Cf ^ 2 * Cp + 1, by positivity, ?_⟩
  intro n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hper hd hdd
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let μ := anchoredLaw P (n + 1)
  let ν := loopSizeBiasedLaw P n
  let F := fun y => loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (anchorVector y)
  let K : ℝ := ((n + 1).succPNat : ℝ) * ℓ
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have : IsProbabilityMeasure μ := isProbabilityMeasure_anchoredLaw P (n + 1)
  have : IsProbabilityMeasure (μ.withDensity (fun y => ENNReal.ofReal (loopSizeWeight n y))) :=
    isProbabilityMeasure_loopSizeBiasedLaw P n
  have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hdom : ∀ᵐ y ∂μ, y ∈ anchoredDomain (n + 1) := loopAnchoring_ae_domain P (n + 1)
  have hbound : ∀ᵐ y ∂μ, ‖F y‖ ≤ Cf * C₀ * K ^ B := by
    filter_upwards [hdom] with y hy
    exact hf C₀ (n + 1).succPNat ℓ ψ (anchorVector y) hC₀ (by simp) hℓ hK
      hψ hper hd hdd (loopAnchoring_anchorVector_mem hy) (anchorVector_zero y)
  have hmeas : AEStronglyMeasurable F μ :=
    loopAnchoring_F_aestronglyMeasurable hs hs1 hℓ hχ hψ hχs hper P (n + 1)
  have hF : MemLp F 2 μ := MemLp.of_bound hmeas _ hbound
  have hFw : MemLp F 2 ν := MemLp.of_bound (hmeas.mono_ac hac) _ (hac.ae_le hbound)
  refine ⟨hF, hFw, ?_⟩
  have hmean : |∫ y, F y ∂μ| ≤ Cf * C₀ * K ^ B := by
    have hh := norm_integral_le_of_norm_le_const hbound
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hh
  have hmean2 : (∫ y, F y ∂μ) ^ 2 ≤ (Cf * C₀ * K ^ B) ^ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hmean
    simpa only [← sq, sq_abs] using hh
  have htail : ν {y | K ^ ε < loopSizeWeight n y} ≤
      ENNReal.ofReal (Cp * K ^ (-(2 * B + 10))) := by
    apply (measure_mono (fun y hy => ?_)).trans
      (hp n ℓ hℓ hℓ1 (by simpa only [Nat.succPNat_coe] using hK))
    change loopCutoff s γ ε (n + 1).succPNat ℓ (anchorVector y) ≠ 1
    rw [loopAnchoring_cutoff_zero hℓ hK (by linarith : 0 ≤ γ) y hy.le]
    norm_num
  have hvar := sizeBiased_variance_le μ (measurable_loopSizeWeight n) hF hFw
    (Real.rpow_nonneg hK0.le ε) (ae_of_all _ fun y hy =>
      loopAnchoring_F_zero hℓ hK (by linarith : 0 ≤ γ) χ ψ y hy.le)
  apply hvar.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ENNReal.ofReal ((Cf * C₀ * K ^ B) ^ 2) *
        ENNReal.ofReal (Cp * K ^ (-(2 * B + 10))) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hmean2) htail
    _ = ENNReal.ofReal (Cf ^ 2 * Cp * C₀ ^ 2 * K ^ (-10 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      have he : (K ^ B) ^ 2 * K ^ (-(2 * B + 10)) = K ^ (-10 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
        congr 1
        norm_num
        ring
      calc (Cf * C₀ * K ^ B) ^ 2 * (Cp * K ^ (-(2 * B + 10))) =
          Cf ^ 2 * Cp * C₀ ^ 2 * ((K ^ B) ^ 2 * K ^ (-(2 * B + 10))) := by ring
        _ = _ := by rw [he]
    _ ≤ ENNReal.ofReal ((Cf ^ 2 * Cp + 1) * C₀ ^ 2 * K ^ (-10 : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      linarith

end Riesz1.Internal

end
