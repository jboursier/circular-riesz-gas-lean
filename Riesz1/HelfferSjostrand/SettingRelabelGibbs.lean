/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingRelabelVolume
public import Riesz1.HelfferSjostrand.SettingGibbs

/-!
# Cyclic change of variables for a labelled Gibbs law

Relabeling sends the original Gibbs probability to the Gibbs probability
of the reflected pair family. The partition functions agree. This proves
the measure transport used in Lemma 3.9 without assuming
permutation symmetry of the pair potentials.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The Hamiltonian of a fundamental representative is its lift Hamiltonian. -/
theorem hsFundamentalHamiltonian_representative (χ : HsPairPotentials N c)
    (x : hsChamber N) :
    hsFundamentalHamiltonian χ (hsRepresentative x) = hsPairExpression χ x.val := by
  have he : WithLp.toLp 2 (hsRepresentative x).val =
      hsTranslate (-(⌊x.val ⟨0, N.pos⟩⌋ : ℝ)) x.val := by
    ext i
    simp only [hsRepresentative_apply, hsTranslate_apply]
    ring
  change hsPairExpression χ (WithLp.toLp 2 (hsRepresentative x).val) = _
  rw [he, hsPairExpression_translate]

/-- The reflected pair Hamiltonian pulls back to the original Hamiltonian. -/
theorem hsFundamentalHamiltonian_relabel (χ : HsPairPotentials N c) (k : ℕ)
    (X : Configuration N) :
    hsFundamentalHamiltonian (hsRelabelPairs χ k) (hsRelabelConfiguration N k X) =
      hsFundamentalHamiltonian χ X := by
  rw [hsRelabelConfiguration, hsFundamentalHamiltonian_representative,
    hsPairExpression_relabel]
  rfl

/-- Exact change of variables for the unnormalized Gibbs weights. -/
theorem hsFundamentalWeight_map_relabel (χ : HsPairPotentials N c) (k : ℕ) :
    (hsFundamentalWeight χ).map (hsRelabelConfiguration N k) =
      hsFundamentalWeight (hsRelabelPairs χ k) := by
  let w := fun X => ENNReal.ofReal
    (Real.exp (-hsFundamentalHamiltonian (hsRelabelPairs χ k) X))
  have hw : Measurable w := ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (continuous_hsFundamentalHamiltonian _).measurable.neg)
  have he : (fun X => w (hsRelabelConfiguration N k X)) =
      (fun X => ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))) := by
    funext X
    dsimp [w]
    rw [hsFundamentalHamiltonian_relabel]
  rw [hsFundamentalWeight, ← he, map_withDensity_comp _
    (measurable_hsRelabelConfiguration N k) hw,
    (measurePreserving_hsRelabelConfiguration N k).map_eq]
  rfl

/-- Relabeling preserves the partition function, with its original normalization. -/
theorem hsPartitionFunction_relabel (χ : HsPairPotentials N c) (k : ℕ) :
    hsPartitionFunction (hsRelabelPairs χ k) = hsPartitionFunction χ := by
  rw [hsPartitionFunction, ← hsFundamentalWeight_map_relabel,
    Measure.map_apply (measurable_hsRelabelConfiguration N k) MeasurableSet.univ,
    preimage_univ]
  rfl

/-- The cyclic change of variables for the normalized general pair Gibbs law. -/
theorem hsGibbsProbability_map_relabel (χ : HsPairPotentials N c) (hc : 0 < c) (k : ℕ) :
    (hsGibbsProbability χ hc : Measure _).map (hsRelabelConfiguration N k) =
      (hsGibbsProbability (hsRelabelPairs χ k) hc : Measure _) := by
  change ((hsPartitionFunction χ)⁻¹ • hsFundamentalWeight χ).map _ =
    (hsPartitionFunction (hsRelabelPairs χ k))⁻¹ • hsFundamentalWeight (hsRelabelPairs χ k)
  rw [Measure.map_smul, hsFundamentalWeight_map_relabel, hsPartitionFunction_relabel]
  exact (measurable_hsRelabelConfiguration N k).aemeasurable

/-- The relabeling on the actual cyclic quotient. -/
def hsRelabelQuotient (N : ℕ+) (k : ℕ) (x : HsConfiguration N) : HsConfiguration N :=
  hsConfigurationMap N (hsRelabelConfiguration N k ((hsConfigurationEquiv N).symm x))

theorem measurable_hsRelabelQuotient (N : ℕ+) (k : ℕ) :
    Measurable (hsRelabelQuotient N k) :=
  (measurable_hsConfigurationMap N).comp
    ((measurable_hsRelabelConfiguration N k).comp (measurable_hsConfigurationEquiv_symm N))

/-- The quotient Gibbs laws obey the same cyclic change of variables. -/
theorem hsQuotientGibbsProbability_map_relabel (χ : HsPairPotentials N c)
    (hc : 0 < c) (k : ℕ) :
    (hsQuotientGibbsProbability χ hc : Measure _).map (hsRelabelQuotient N k) =
      (hsQuotientGibbsProbability (hsRelabelPairs χ k) hc : Measure _) := by
  rw [hsQuotientGibbsProbability_eq_map,
    Measure.map_map (measurable_hsRelabelQuotient N k) (measurable_hsConfigurationMap N)]
  have he : hsRelabelQuotient N k ∘ hsConfigurationMap N =
      hsConfigurationMap N ∘ hsRelabelConfiguration N k := by
    funext X
    change hsConfigurationMap N (hsRelabelConfiguration N k
      ((hsConfigurationEquiv N).symm ((hsConfigurationEquiv N) X))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [he, ← Measure.map_map (measurable_hsConfigurationMap N)
    (measurable_hsRelabelConfiguration N k), hsGibbsProbability_map_relabel,
    ← hsQuotientGibbsProbability_eq_map]

end Riesz1

end
