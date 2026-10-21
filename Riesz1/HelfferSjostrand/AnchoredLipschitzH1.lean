/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredCalculus
public import Riesz1.ToMathlib.WeightedSobolev.LipschitzH1Product

/-!
# Lipschitz functions and cutoff products for the anchored law

The anchored completion contains functions Lipschitz near the
closed simplex and cutoff products with coefficients `C¹` only near their
support. The latter is the membership step in Lemma 5.2 and Proposition 5.9.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The Euclidean anchored law is absolutely continuous with respect to
Lebesgue measure, also in dimension zero. -/
theorem anchoredMeasureE_absolutelyContinuous (χ : HsPairPotentials n.succPNat c) :
    anchoredMeasureE χ ≪ volume := by
  have hac : hsAnchoredLaw χ ≪ volume := by
    unfold hsAnchoredLaw hsAnchoredWeight
    exact (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)).trans
      Measure.absolutelyContinuous_restrict
  have he : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → AnchoredEuclidean n) :=
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.measurableEmbedding
  have hm := he.absolutelyContinuous_map hac
  rwa [(PiLp.volume_preserving_toLp (Fin n)).map_eq] at hm

/-- Globally Lipschitz functions lie in the anchored Sobolev space. -/
theorem isAnchoredH1_of_lipschitz (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) :
    IsAnchoredH1 χ F (gradient F) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact WeightedSobolev.isWeightedH1_of_lipschitz (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex χ) (anchoredMeasureE_absolutelyContinuous χ) hF

/-- Lipschitz regularity only near the closed simplex suffices. -/
theorem isAnchoredH1_of_lipschitzOn (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {C : ℝ≥0} {W : Set (AnchoredEuclidean n)}
    (hW : IsOpen W) (hUW : closure (anchoredSimplex n) ⊆ W)
    (hF : LipschitzOnWith C F W) : IsAnchoredH1 χ F (gradient F) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact WeightedSobolev.isWeightedH1_of_lipschitzOn (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex χ) (anchoredMeasureE_absolutelyContinuous χ) hW hUW hF

/-- Local Lipschitz regularity near the closed simplex suffices. -/
theorem isAnchoredH1_of_locallyLipschitzOn (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {W : Set (AnchoredEuclidean n)}
    (hW : IsOpen W) (hUW : closure (anchoredSimplex n) ⊆ W)
    (hF : LocallyLipschitzOn W F) : IsAnchoredH1 χ F (gradient F) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact WeightedSobolev.isWeightedH1_of_locallyLipschitzOn (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex χ) (anchoredMeasureE_absolutelyContinuous χ) hW hUW hF

/-- Anchored Sobolev membership of a cutoff product with its actual product
gradient. The coefficient is unrestricted outside a neighborhood of the
intersection of the cutoff support and the closed simplex. -/
theorem isAnchoredH1_cutoff_mul (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {η F : AnchoredEuclidean n → ℝ} {C : ℝ≥0} {W O : Set (AnchoredEuclidean n)}
    (hW : IsOpen W) (hUW : closure (anchoredSimplex n) ⊆ W) (hη : LipschitzOnWith C η W)
    (hO : IsOpen O) (hSO : tsupport η ∩ closure (anchoredSimplex n) ⊆ O)
    (hF : ContDiffOn ℝ 1 F O) :
    IsAnchoredH1 χ (fun x => η x * F x)
      (fun x => η x • gradient F x + F x • gradient η x) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact WeightedSobolev.isWeightedH1_cutoff_mul (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex χ) (anchoredMeasureE_absolutelyContinuous χ) hW hUW hη hO hSO hF

end Riesz1

end
