/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.StrictConvRepresentation
public import Riesz1.HelfferSjostrand.AnchoredInverseEnergy
public import Riesz1.Frozen.Variance

/-!
# The variance representation used in the a priori bound

The diagonal case of Remark 3.2 identifies the
actual anchored inverse energy of a Sobolev gradient with its variance.
Both the real variance and the extended variance are treated.
The last helper is the energy splitting step in the proof of Lemma 5.2.
These are internal Sobolev helpers, not assertions of the final bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

variable {n : ℕ} {c : ℝ}

/-- The diagonal anchored representation, as an equality of real
variance and the inverse energy. This is the diagonal case of Remark 3.2.
-/
theorem anchored_variance_eq_inverseEnergy (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) (hPL : External.PrekopaLeindler) (hn : 0 < n)
    {C_N : ℝ} (hadm : HsAdmissible χ C_N) (F : AnchoredSobolev χ) :
    ProbabilityTheory.variance F.val.1 (anchoredMeasureE χ) =
      anchoredInverseEnergy χ hc F.val.2 := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hrep := (anchoredRepresentation χ hc hPL hn hadm F F).2.2
  rw [ProbabilityTheory.variance_eq_integral (Lp.memLp F.val.1).aemeasurable]
  simp only [pow_two]
  rw [hrep]
  exact (L2.inner_def F.val.2
    (anchoredVectorValues (anchoredMeasureE χ) χ (anchoredInverse χ hc F.val.2))).symm

/-- The same identity for the extended variance, including the
required first-moment validity. See Remark 3.2. -/
theorem anchored_frozenVariance_eq_inverseEnergy (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) (hPL : External.PrekopaLeindler) (hn : 0 < n)
    {C_N : ℝ} (hadm : HsAdmissible χ C_N) (F : AnchoredSobolev χ) :
    ∃ hF : Integrable F.val.1 (anchoredMeasureE χ),
      Riesz1.variance (anchoredMeasureE χ) F.val.1 hF =
        ENNReal.ofReal (anchoredInverseEnergy χ hc F.val.2) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  refine ⟨(Lp.memLp F.val.1).integrable one_le_two, ?_⟩
  rw [Riesz1.variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
    ← ProbabilityTheory.ofReal_variance (Lp.memLp F.val.1),
    anchored_variance_eq_inverseEnergy χ hc hPL hn hadm F]

/-- The precise two-field splitting used for `∇(ηF) = η∇F + F∇η`.
The Sobolev membership and the product identity must be established
when applying this internal helper. It is used in the proof of Lemma 5.2.
-/
theorem anchored_variance_le_split_inverseEnergy (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) (hPL : External.PrekopaLeindler) (hn : 0 < n)
    {C_N : ℝ} (hadm : HsAdmissible χ C_N) (F : AnchoredSobolev χ)
    (v w : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ))
    (hgrad : F.val.2 = v + w) :
    ProbabilityTheory.variance F.val.1 (anchoredMeasureE χ) ≤
      2 * anchoredInverseEnergy χ hc v + 2 * anchoredInverseEnergy χ hc w := by
  rw [anchored_variance_eq_inverseEnergy χ hc hPL hn hadm F, hgrad]
  exact (anchoredInverse_symmetry_positivity_subadditivity χ hc).2.2.2.1 v w

end Riesz1.Internal

end
