/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffEnergy
public import Riesz1.Variance.APrioriCutoffL2

/-!
# Complete negligible cutoff lemma

Both conclusions of the negligible cutoff step in the proof of Lemma 5.2, with one common
bound chosen before the particle number, cutoff, scale, and statistic.
Rigidity is obtained from the Bakry–Émery criterion `External.BakryEmery` and the
Prékopa–Leindler inequality `External.PrekopaLeindler`, which are explicit hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- **Complete statement of the negligible cutoff step.** The first
clause allows the bound on the statistic only on the support of
the gradient (in fact only at its nonzero points). The second clause
uses a global bound. The inverse and law are the actual tilted ones. -/
theorem a_priori_cutoff_complete (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε)
    (D M b : ℝ) (hD : 0 < D) (hM : 0 < M) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ),
      ∀ (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → ∀ (hK : 1 ≤ ((n : ℝ) + 1) * ℓ),
      let K := ((n : ℝ) + 1) * ℓ
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      (∀ (T : (Fin n → ℝ) → ℝ), Measurable T →
        (∀ y, fderiv ℝ (anchoredCutoff n.succPNat P.val.2 K γ ε) y ≠ 0 → |T y| ≤ M * K ^ D) →
        ∃ hv : MemLp (anchoredCutoffField n P.val.2 K γ ε T) 2 (anchoredMeasureE χ),
          anchoredInverseEnergy χ
            (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
            (hv.toLp (anchoredCutoffField n P.val.2 K γ ε T)) ≤ C * K ^ (-b)) ∧
      (∀ (T : (Fin n → ℝ) → ℝ), Measurable T → (∀ y, |T y| ≤ M * K ^ D) →
        eLpNorm (fun y => (1 - anchoredCutoff n.succPNat P.val.2 K γ ε y) * T y) 2
          ((gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)) ≤ ENNReal.ofReal (C * K ^ (-b))) := by
  obtain ⟨C₁, hC₁, hE⟩ := anchoredCutoff_energy hBE hPL P γ ε hγ hε D M b hD hM hb
  obtain ⟨C₂, hC₂, hL⟩ := Internal.anchoredCutoff_L2_of_rigidity P.val.1 P.val.2
    P.2.1 P.2.2.1 P.2.2.2 (Internal.rigidityConclusion_of_externals hBE hPL _ _ _ _ _)
    γ ε hγ hε D M b hD hM hb
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, fun n hn θ hθ ℓ hℓ hℓ1 hK => ?_⟩
  have hKN : ((n : ℝ) + 1) * ℓ ≤ (n : ℝ) + 1 :=
    mul_le_of_le_one_right (by positivity) hℓ1
  have hp : 0 ≤ (((n : ℝ) + 1) * ℓ) ^ (-b) := Real.rpow_nonneg (by positivity) _
  constructor
  · intro T hTm hT
    obtain ⟨hv, h⟩ := hE n hn θ hθ _ hK hKN T hTm hT
    exact ⟨hv, h.trans (mul_le_mul_of_nonneg_right (show C₁ ≤ C₁ + C₂ by linarith) hp)⟩
  · intro T hTm hT
    have h := hL hPL n.succPNat ℓ (by simpa using hn) hℓ hℓ1 (by simpa using hK) T hTm
      (by simpa using hT)
    have h' : eLpNorm (fun y => (1 - anchoredCutoff n.succPNat P.val.2
        (((n : ℝ) + 1) * ℓ) γ ε y) * T y) 2
        ((gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)) ≤
        ENNReal.ofReal (C₂ * (((n : ℝ) + 1) * ℓ) ^ (-b)) := by
      simpa only [Nat.succPNat_coe, Nat.cast_succ] using h
    exact h'.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (show C₂ ≤ C₁ + C₂ by linarith) hp))

end Riesz1

end
