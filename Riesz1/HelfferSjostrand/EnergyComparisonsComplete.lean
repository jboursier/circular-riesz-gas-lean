/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.EnergyComparisonsVariance

/-!
# Comparison of variances and energies: the whole of Lemma 3.5

Lemma 3.5, both assertions, for the anchored law `μ*` of the Gibbs
measure with `N = n + 1 ≥ 2` particles. The integer `n` is `N - 1`, as in the anchored API.

* Variance: if `F, G ∈ H¹(μ*)` satisfy `|∂_i F| ≤ ∂_i G` for every coordinate, then
  `Var_{μ*} F ≤ Var_{μ*} G`, with `Riesz1.variance`.
* Energy: if `v, w ∈ L²(μ*; ℝ^{N-1})` satisfy `|v_i| ≤ w_i` for every coordinate, then
  `𝒥_{μ*}(v) ≤ 𝒥_{μ*}(w)`.

The Prékopa–Leindler inequality `External.PrekopaLeindler` enters as an explicit hypothesis.
Admissibility of `H` gives `N ≥ 2` and `c > 0`, which the variance assertion uses.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- Lemma 3.5, complete. For every admissible `H` with `N = n + 1`
particles and `c > 0`, the variance and the energy comparisons hold on the anchored law `μ*`. -/
theorem energy_comparisons (hPL : External.PrekopaLeindler) (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) {C_N : ℝ} (hadm : HsAdmissible χ C_N) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    (∀ F G : AnchoredSobolev χ,
      (∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), |F.val.2 y i| ≤ G.val.2 y i) →
        Riesz1.variance (anchoredMeasureE χ) ⇑F.val.1
            ((Lp.memLp F.val.1).integrable one_le_two) ≤
          Riesz1.variance (anchoredMeasureE χ) ⇑G.val.1
            ((Lp.memLp G.val.1).integrable one_le_two)) ∧
    (∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      (∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), |v y i| ≤ w y i) →
        anchoredInverseEnergy χ hc v ≤ anchoredInverseEnergy χ hc w) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact ⟨fun F G hFG => anchoredVariance_mono_of_grad_abs_le χ hc hPL hadm F G hFG,
    fun v w hvw => anchoredInverseEnergy_mono_of_abs_le χ hc v w hvw⟩

end Riesz1

end
