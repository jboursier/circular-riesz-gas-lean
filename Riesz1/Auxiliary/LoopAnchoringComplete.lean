/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringL2
public import Riesz1.Auxiliary.LoopLocalizationExponent

/-!
# Anchoring and removal of size weighting

Both assertions of the anchoring part of Lemma 5.8, with finite
second moments and only the Bakry–Émery criterion `External.BakryEmery` and the
Prékopa–Leindler inequality `External.PrekopaLeindler` as analytic inputs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

/-- The anchoring part of Lemma 5.8, every assertion. The threshold
and exponent precede `β` and `χ` to express their dependence only on `s, α, γ`.
The multiplicative constant precedes `N, ℓ, C₀, ψ`. Particle numbers are
`N = n + 2`, covering exactly all integers at least two. -/
theorem loopAnchoring_uniform {s α γ : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hα : s - 1 ≤ α) (hα2 : α < s / 2)
    (hγ : loopLocalizationExponent s ≤ γ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ (β : ℝ) (hβ : 0 < β) (_hBE : External.BakryEmery) (_hPL : External.PrekopaLeindler)
        (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ε < εstar → ∃ C : ℝ, 0 < C ∧
          ∀ (n : ℕ) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
            0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ C₀ →
            ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
            (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
              (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
            (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
              (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
            let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
            letI := isProbabilityMeasure_anchoredLaw P (n + 1)
            let μ := loopPrecedingMeasure P (n + 1).succPNat
            let K : ℝ := ((n + 1).succPNat : ℝ) * ℓ
            let F := fun y => loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (anchorVector y)
            let E := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
              loopLocalLoop s (n + 1).succPNat ℓ γ (loopLocalTransport χ (n + 1).succPNat ℓ γ ψ) X -
                loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (loopPrecedingY X)
            ∃ hF : MemLp F 2 (anchoredLaw P (n + 1)),
            ∃ hFw : MemLp F 2 (loopSizeBiasedLaw P n),
              MemLp E 2 μ ∧
              eLpNorm E 2 μ ≤ ENNReal.ofReal (C * C₀ * K ^ (1 - s + α + κ * ε)) ∧
              variance (loopSizeBiasedLaw P n) F (hFw.integrable one_le_two) ≤
                ENNReal.ofReal (K ^ ε) *
                  variance (anchoredLaw P (n + 1)) F (hF.integrable one_le_two) +
                    ENNReal.ofReal (C * C₀ ^ 2 * K ^ (-10 : ℝ)) := by
  have hγ4 : 4 ≤ γ := (loopLocalizationExponent_ge_four s).trans hγ
  have hγ1 : 1 < γ := by linarith
  have hγs : 2 / s ≤ γ := by
    have hh : 4 / s ≤ γ := ((le_max_right 4 (4 / s)).trans
      (le_max_left (max 4 (4 / s)) ((3 / 2 - s) / (1 - s)))).trans hγ
    exact (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) hs.le).trans hh
  obtain ⟨εL, hεL, κ, hκ, hl2⟩ := loopAnchoring_l2 hs hs1 hα hα2 (max_le hγ4 hγs)
  refine ⟨min εL (min (1 / 8) ((1 - s / 2) / 8)), by
    have : 0 < (1 - s / 2) / 8 := by linarith
    positivity, κ, hκ, ?_⟩
  intro β hβ hBE hPL χ hχ hχc hχs hχ1 hχ01 ε hε hεstar
  have hεL' := hεstar.trans_le (min_le_left _ _)
  have hεs := hεstar.trans_le (min_le_right _ _)
  obtain ⟨CL, hCL, hL⟩ := hl2 β hβ hBE hPL χ hχ hχc hχs hχ1 hχ01 ε hε hεL'
  obtain ⟨CV, hCV, hV⟩ := Internal.loopAnchoring_sizeWeighted_variance β s α γ ε
    hβ hs hs1 hα hα2 hγ1 hε hεs hBE hPL hχ hχc hχs hχ1 hχ01
  refine ⟨CL + CV, by linarith, ?_⟩
  intro n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hp hd hdd
  obtain ⟨hF, hFw, hv⟩ := hV n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hp hd hdd
  obtain ⟨hE, he⟩ := hL n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hp hd hdd
  refine ⟨hF, hFw, hE, he.trans ?_, hv.trans ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    gcongr
    linarith
  · apply add_le_add le_rfl
    apply ENNReal.ofReal_le_ofReal
    gcongr
    linarith

/-- The anchoring part of Lemma 5.8, in the order of the paper: fixed
parameters and cutoff, then `εstar, κ`, then `ε, C`, then particle number,
scale, envelope constant and transport. The uniform theorem above certifies
that `εstar, κ` depend only on `s, α, γ`. -/
theorem auxiliary_Loop_anchoring (β s α γ : ℝ)
    (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : loopLocalizationExponent s ≤ γ)
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < εstar → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
        0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ C₀ →
        ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
        (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
          (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
        (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
          (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
        let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
        letI := isProbabilityMeasure_anchoredLaw P (n + 1)
        let μ := loopPrecedingMeasure P (n + 1).succPNat
        let K : ℝ := ((n + 1).succPNat : ℝ) * ℓ
        let F := fun y => loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (anchorVector y)
        let E := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
          loopLocalLoop s (n + 1).succPNat ℓ γ (loopLocalTransport χ (n + 1).succPNat ℓ γ ψ) X -
            loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (loopPrecedingY X)
        ∃ hF : MemLp F 2 (anchoredLaw P (n + 1)),
        ∃ hFw : MemLp F 2 (loopSizeBiasedLaw P n),
          MemLp E 2 μ ∧
          eLpNorm E 2 μ ≤ ENNReal.ofReal (C * C₀ * K ^ (1 - s + α + κ * ε)) ∧
          variance (loopSizeBiasedLaw P n) F (hFw.integrable one_le_two) ≤
            ENNReal.ofReal (K ^ ε) *
              variance (anchoredLaw P (n + 1)) F (hF.integrable one_le_two) +
                ENNReal.ofReal (C * C₀ ^ 2 * K ^ (-10 : ℝ)) := by
  obtain ⟨εstar, hεstar, κ, hκ, h⟩ := loopAnchoring_uniform hs hs1 hα hα2 hγ
  exact ⟨εstar, hεstar, κ, hκ, h β hβ hBE hPL χ hχ hχc hχs hχ1 hχ01⟩

end Riesz1

end
