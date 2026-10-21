/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.NondegeneracyZero
public import Riesz1.Bridges.FluctuationSquare
public import Riesz1.Frozen.Variance

/-!
# The conclusion of uniform quantitative variance

The conditional interface for the uniform form of Theorem 2.
The two tests are the actual pullbacks of the convolution and its difference,
using `cltScaledLift`, rather than new profile or regularization definitions.
The support radius is part of the original compact profile data. In the
macroscopic alternative it is unused. Taking `t ≤ t₀ < 1/2 - r` recovers
exactly the parameter range.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1.Internal

/-- Both families in the uniform form of Theorem 2, with a common
constant chosen before the scale sequence, smoothing radius and particle
number. Finiteness is recorded before either extended variance is converted
to a real number. No main theorem or external proof is imported. -/
def QuantitativeVarianceUniformConclusion : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (r : ℝ)
    (_hr : 0 < r) (_hrhalf : r < 1 / 2) (ε : ℝ) (_hε : 0 < ε),
    ∃ C : ℝ, 0 < C ∧
      ∀ (ell : Scales), Admissible P p ell α d →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        ((∀ M, (ell M).val = 1) ∨
          ((∀ᵐ x : ℝ, r ≤ |x| → zeroExtension p x = 0) ∧ t < 1 / 2 - r)) →
      ∀ (N : ℕ+), 1 ≤ (N : ℝ) * (ell N).val →
      ∀ v : Profile,
        ((∀ x, v.val x = cltScaledLift hρ (ell N) ht
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x) ∨
          (∀ x, v.val x = testAtScale p (ell N) x - cltScaledLift hρ (ell N) ht
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x)) →
        let hv : MemLp v.val 2 volume := by
          have hv := v.property.re
          change MemLp (fun x => (v.val x : ℂ).re) 2 volume at hv
          simpa only [Complex.ofReal_re] using hv
        let hF := memLp_fluctuation P N hv
        let V := variance (gibbsMeasure P N)
          (fun X : Configuration N => fluctuation ⟨v.val, hv.integrable one_le_two⟩ X)
          (by
            have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
            exact hF.integrable one_le_two)
        let σ := cltVariance P (ell N) ⟨(fun x => (v.val x : ℂ)), v.property⟩
        V < ⊤ ∧ σ < ⊤ ∧
          |V.toReal - ((N : ℝ) * (ell N).val) ^ P.val.2 * σ.toReal| ≤
            C * ((N : ℝ) * (ell N).val) ^ (max (2 * P.val.2 - 1) (2 * α) + ε)

end Riesz1.Internal
