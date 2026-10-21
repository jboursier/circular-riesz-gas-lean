/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlGapEnergy
public import Riesz1.Variance.VarAlGapCutoffEnergy

/-!
# Gap and cutoff energies for the loop

Both assertions of Proposition 5.9, with one common coefficient. The loss
exponent is selected before the inverse temperature, envelope amplitude,
spatial cutoff and epsilon. The two fields belong to the actual vector
`L²` carrier of the convexified anchored law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- **Proposition 5.9, gap assertions, complete.** Here `N = n + 1`,
`Q` is the convexification on `I_{2γ}`, `v = η* W*`, and
`w = Loop* ∇η*`. The result holds for every `γ > 1`. An explicit small-epsilon
range is supplied. The only external inputs are `External.BakryEmery` and
`External.PrekopaLeindler`. -/
theorem varAl_gap (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    {s α γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα : s - 1 < α) (hα2 : α < s / 2) (hγ : 1 < γ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (β : ℝ) (hβ : 0 < β),
      let P : Parameters := ⟨(β, s), hβ, hs0, hs1⟩
      ∀ (C₀ : ℝ), 0 < C₀ → ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ε < min (1 / 8) ((1 - s / 2) / 8) →
          ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
            ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (ℓ : ℝ),
              0 < ℓ → ℓ ≤ 1 → ∀ (hK : 1 ≤ (n.succPNat : ℝ) * ℓ),
              ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
                (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
                  ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
                (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
                  ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
                let K := (n.succPNat : ℝ) * ℓ
                let Q := nearestTiltedPairs P n.succPNat hθ K (2 * γ) ε (by linarith)
                let v := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
                  loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) *
                    gradWfield s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
                      (anchorVector (WithLp.ofLp y)) i.succ
                let w := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
                  gradLoop s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
                    (anchorVector (WithLp.ofLp y)) *
                  fderiv ℝ (fun z => loopCutoff s γ ε n.succPNat ℓ (anchorVector z))
                    (WithLp.ofLp y) (Pi.single i (1 : ℝ))
                ∃ hv : MemLp v 2 (anchoredMeasureE Q),
                  ∃ hw : MemLp w 2 (anchoredMeasureE Q),
                    anchoredInverseEnergy Q
                      (hsRieszPairPotentials_curvature_pos n.succPNat hβ (parametersExponent P))
                      (hv.toLp v) ≤ C * K ^ (κ * ε) * (K + K ^ (2 * (1 - s + α))) ∧
                    anchoredInverseEnergy Q
                      (hsRieszPairPotentials_curvature_pos n.succPNat hβ (parametersExponent P))
                      (hw.toLp w) ≤ C * K ^ (-10 : ℝ) := by
  obtain ⟨κ, hκ, hgap⟩ := varAl_gap_energy hs0 hs1 hα.le hα2 hγ
  refine ⟨κ, hκ, ?_⟩
  intro β hβ P C₀ hC₀ χ hχ hχc hχs hχ1 hχ01 ε hε hεs
  obtain ⟨Cg, hCg, hg⟩ := hgap β hβ χ hχ hχc hχs hχ1 hχ01 ε hε hεs
  have hεs' : ε ≤ 1 - s / 2 := by
    have := lt_of_lt_of_le hεs (min_le_right (1 / 8) ((1 - s / 2) / 8))
    linarith
  obtain ⟨Cb, hCb, hb⟩ := varAl_gap_cutoff_energy hBE hPL P hα.le hα2 hγ hε hεs' hC₀
    (show (0 : ℝ) < 10 by norm_num) hχ hχc hχs hχ1 hχ01
  refine ⟨Cg * C₀ ^ 2 + Cb, by positivity, ?_⟩
  intro n hn θ hθ ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  obtain ⟨hv, hvE⟩ := hg n hn θ hθ ℓ C₀ ψ hℓ hℓ1 hK hC₀.le hψ hp h1 h2
  obtain ⟨hw, hwE⟩ := hb n hn θ hθ ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  refine ⟨hv, hw, ?_, ?_⟩
  · exact hvE.trans (by
      have hnonneg : 0 ≤ ((n.succPNat : ℝ) * ℓ) ^ (κ * ε) *
          ((n.succPNat : ℝ) * ℓ + ((n.succPNat : ℝ) * ℓ) ^ (2 * (1 - s + α))) := by positivity
      nlinarith [mul_nonneg hCb.le hnonneg])
  · exact hwE.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_nonneg hCg.le (sq_nonneg C₀)]) (by positivity))

end Riesz1

end
