/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientInverse
public import Riesz1.HelfferSjostrand.AnchoredInverseEnergy

/-!
# Symmetry, positivity and sub-additivity of the inverse

This file proves the quotient and anchored parts together. The integer `n` is `N - 1`, so the
Hamiltonian `χ` lives on `N = n + 1` particles, as in the anchored API. The quotient clauses are
those of `Riesz1/HelfferSjostrand/QuotientInverse.lean`. The anchored clauses are
`Riesz1.anchoredInverse_symmetry_positivity_subadditivity`.

The lemma takes the Prékopa–Leindler inequality `External.PrekopaLeindler` as an explicit
hypothesis, which the inverse of the quotient needs. Admissibility is not needed for these clauses.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

variable (hPL : External.PrekopaLeindler) (χ : HsPairPotentials n.succPNat c)
  (hN : 2 ≤ (n.succPNat : ℕ)) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration n.succPNat))

/-- For the quotient Gibbs probability `μ` and its inverse `T`:

* `T` is linear.
* `∫ v · Tw dμ = ∫ w · Tv dμ`.
* `𝒥_μ(v) ≥ 0`.
* `𝒥_μ(v + w) ≤ 2𝒥_μ(v) + 2𝒥_μ(w)`.
* `𝒥_μ(a + b + d) ≤ 4𝒥_μ(a) + 4𝒥_μ(b) + 2𝒥_μ(d)`.

The same five assertions hold for the
anchored law `μ*` and `T*`, with no compatibility condition. -/
theorem symmetry_positivity_subadditivity :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    (∀ (a b : ℝ) (v w : hsMeanZeroL2 μ),
      hsInverse hPL χ hN hc (a • v + b • w) =
        a • hsInverse hPL χ hN hc v + b • hsInverse hPL χ hN hc w) ∧
    (∀ v w : hsMeanZeroL2 μ,
      ∫ x, ∑ i : Fin (n.succPNat : ℕ), v.val x i *
          hsJetValue μ i (hsInverse hPL χ hN hc w).val.val x ∂μ =
        ∫ x, ∑ i : Fin (n.succPNat : ℕ), w.val x i *
          hsJetValue μ i (hsInverse hPL χ hN hc v).val.val x ∂μ) ∧
    (∀ v : hsMeanZeroL2 μ, 0 ≤ hsInverseEnergy hPL χ hN hc v) ∧
    (∀ v w : hsMeanZeroL2 μ,
      hsInverseEnergy hPL χ hN hc (v + w) ≤
        2 * hsInverseEnergy hPL χ hN hc v + 2 * hsInverseEnergy hPL χ hN hc w) ∧
    (∀ a b d : hsMeanZeroL2 μ,
      hsInverseEnergy hPL χ hN hc (a + b + d) ≤
        4 * hsInverseEnergy hPL χ hN hc a + 4 * hsInverseEnergy hPL χ hN hc b +
          2 * hsInverseEnergy hPL χ hN hc d) ∧
    (∀ (a b : ℝ) (v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)),
      anchoredInverse χ hc (a • v + b • w) =
        a • anchoredInverse χ hc v + b • anchoredInverse χ hc w) ∧
    (∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      ∫ y, inner ℝ (v y) (anchoredVectorValues (anchoredMeasureE χ) χ
          (anchoredInverse χ hc w) y) ∂(anchoredMeasureE χ) =
        ∫ y, inner ℝ (w y) (anchoredVectorValues (anchoredMeasureE χ) χ
          (anchoredInverse χ hc v) y) ∂(anchoredMeasureE χ)) ∧
    (∀ v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ), 0 ≤ anchoredInverseEnergy χ hc v) ∧
    (∀ v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc (v + w) ≤
        2 * anchoredInverseEnergy χ hc v + 2 * anchoredInverseEnergy χ hc w) ∧
    (∀ a b d : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc (a + b + d) ≤
        4 * anchoredInverseEnergy χ hc a + 4 * anchoredInverseEnergy χ hc b +
          2 * anchoredInverseEnergy χ hc d) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact ⟨hsInverse_linear hPL χ hN hc, hsInverse_integral_symm hPL χ hN hc,
    hsInverseEnergy_nonneg hPL χ hN hc, hsInverseEnergy_subadd hPL χ hN hc,
    hsInverseEnergy_subadd_three hPL χ hN hc,
    anchoredInverse_symmetry_positivity_subadditivity χ hc⟩

end Riesz1

end
