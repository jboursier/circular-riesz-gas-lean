/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonBound
public import Riesz1.Variance.APrioriComparisonControl
public import Riesz1.Variance.APrioriComparisonAdmissible

/-!
# Both a priori comparison energy estimates

Part of Lemma 5.2, the energy assertion and its
augmented version. The cutoff comparator variance and its cutoff-gradient
energy control the dominated field. All scales `K ≥ 1` are allowed, generalizing `K = Nℓ ≤ N`.
The only hypotheses are the Bakry–Émery criterion `hBE` and the Prékopa–Leindler
inequality `hPL`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Classical
open scoped ENNReal

namespace Riesz1

/-- **Both energy assertions, part of Lemma 5.2.**
The weight is either the original one or the augmented one. One constant
works for both choices, every forcing cutoff, and every measurable field.
The exponent `2a + 4 + 2γ` is independent of `ε`. -/
theorem a_priori_comparison_energy (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam γ M a : ℝ) (hlam : 0 ≤ lam) (hγ : 1 < γ)
    (hM : 0 < M) (_ha : 0 < a) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ),
      ∀ (K : ℝ) (hK : 1 ≤ K), ∀ J : Finset (Fin (n + 1)),
      J ⊆ (window n.succPNat K γ).erase ⟨0, n.succPNat.pos⟩ →
      ∀ w : Fin (n + 1) → ℝ,
        (w = comparisonWeight n.succPNat K P.val.2 lam ε ∨
          w = augmentedComparisonWeight n.succPNat K P.val.2 lam ε) →
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      ∀ (v : AnchoredEuclidean n → AnchoredEuclidean n), Measurable v →
        (∀ i, ∀ᵐ y ∂anchoredMeasureE χ, i.succ ∉ J → v y i = 0) →
        (∀ i, ∀ᵐ y ∂anchoredMeasureE χ,
          anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) * |v y i| ≤
            (M * K ^ (a * ε)) * anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) *
              (((n : ℝ) + 1) * w i.succ)) →
        ∃ hv : MemLp (fun y => anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) • v y)
            2 (anchoredMeasureE χ),
          anchoredInverseEnergy χ
            (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
            (hv.toLp (fun y => anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) • v y)) ≤
              C * K ^ ((2 * a + 4 + 2 * γ) * ε) * (K ^ (2 * lam) + K ^ P.val.2) := by
  obtain ⟨C₀, hC₀, hcontrol⟩ := APrioriComparison.comparator_cutoff_estimates
    hBE hPL P lam γ ε hlam hγ hε hε1
  refine ⟨4 * M ^ 2 * C₀, by positivity, fun n hn θ hθ K hK J hJ w hw v hvm hz hb => ?_⟩
  have hK0 : 0 < K := by linarith
  let χ := nearestTiltedPairs P n.succPNat hθ K γ ε hK0
  have hc := hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P)
  obtain ⟨D, hadm⟩ := APrioriComparison.nearestTiltedPairs_admissible P n.succPNat
    (by simpa using hn) hθ K γ ε hK0
  have hw0 : ∀ i, 0 ≤ w i := by
    rcases hw with rfl | rfl
    · exact fun i => comparisonWeight_nonneg (N := n.succPNat) hK0.le i
    · exact fun i => augmentedComparisonWeight_nonneg (N := n.succPNat) hK0.le i
  obtain ⟨he, hvar, hcut⟩ := hcontrol n hn θ hθ K hK J hJ w hw
  obtain ⟨hv, henergy⟩ := APrioriComparison.cutoff_energy_le_comparator χ hc hPL hn hadm
    P.val.2 K γ ε (M * K ^ (a * ε)) hK hε.le (by positivity) J w hw0 v hvm hz hb he
  refine ⟨hv, henergy.trans ?_⟩
  have hrem : K ^ (-10 : ℝ) ≤
      K ^ ((4 + 2 * γ) * ε) * (K ^ (2 * lam) + K ^ P.val.2) := by
    have h1 : K ^ (-10 : ℝ) ≤ K ^ ((4 + 2 * γ) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hK (by nlinarith)
    have h2 : 1 ≤ K ^ (2 * lam) + K ^ P.val.2 :=
      (Real.one_le_rpow hK (by positivity : 0 ≤ 2 * lam)).trans
        (le_add_of_nonneg_right (by positivity))
    exact h1.trans (le_mul_of_one_le_right (by positivity) h2)
  have hcut' := hcut.trans (mul_le_mul_of_nonneg_left hrem hC₀.le)
  replace hcut' := hcut'.trans_eq
    (mul_assoc C₀ (K ^ ((4 + 2 * γ) * ε)) (K ^ (2 * lam) + K ^ P.val.2)).symm
  have hpow : (K ^ (a * ε)) ^ 2 * K ^ ((4 + 2 * γ) * ε) =
      K ^ ((2 * a + 4 + 2 * γ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
    congr 1
    ring
  calc
    _ ≤ 2 * (M * K ^ (a * ε)) ^ 2 *
        (C₀ * K ^ ((4 + 2 * γ) * ε) * (K ^ (2 * lam) + K ^ P.val.2)) +
        2 * (M * K ^ (a * ε)) ^ 2 *
        (C₀ * K ^ ((4 + 2 * γ) * ε) * (K ^ (2 * lam) + K ^ P.val.2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hvar (by positivity))
        (mul_le_mul_of_nonneg_left hcut' (by positivity))
    _ = (4 * M ^ 2 * C₀) * ((K ^ (a * ε)) ^ 2 * K ^ ((4 + 2 * γ) * ε)) *
        (K ^ (2 * lam) + K ^ P.val.2) := by ring
    _ = _ := by rw [hpow]

end Riesz1

end
