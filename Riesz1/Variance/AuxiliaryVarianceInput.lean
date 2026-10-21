/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryReductionBounds

/-!
# Two microscopic estimates of the variance reduction in Proposition 5.6

Proposition 5.6 reduces the variance error to four estimates. Two of them are
taken as hypotheses here: the microscopic bound of Lemma 5.3 for the mixed statistic
of `ξ - ξ_h`, and the derivative bound of the proof of Proposition 5.6, obtained by
applying Lemma 5.2 to the marked decomposition of `ψ_reg'`. This file states both
on the objects of this development, with the quantifiers of the paper. The
conditional theorem `Riesz1.Internal.auxiliary_variance_reduction_of_input` takes them
as hypotheses. The other two estimates, the smoothing seminorm `S(ξ - ξ_h)` and the
transport energy `J`, enter that theorem as explicit hypotheses too.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- Lemma 5.3 with `h = K⁻¹`, for the periodized profile `ξ` of an
admissible profile at every scale of the sequence: for every `ε > 0` there is `C > 0`,
independent of `N` and of the scale sequence, such that the mixed statistic of `ξ - ξ_h`
is square integrable and has variance at most `C K^ε (K^{2α} + K^{3s-2})`. -/
def AuxiliaryMicroVarianceInput : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (ell : Scales), Admissible P p ell α d → ∀ (N : ℕ+), 1 ≤ cltK N (ell N) →
      let ξ : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))} :=
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
      ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ))) 2
          (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
          ENNReal.ofReal (C * cltK N (ell N) ^ ε *
            (cltK N (ell N) ^ (2 * α) + cltK N (ell N) ^ (3 * P.val.2 - 2)))

/-- The derivative estimate of the proof of Proposition 5.6: for every `ε > 0` there is
`C > 0`, independent of the regularized transport `ψ_h` in the admissible class, such that
the statistic `Fluct_N[ψ_h'(ℓ⁻¹ ·)]` is square integrable and has variance at most
`C K^ε (K^s + K^{2b})` with `b = 1 - s + α`. Here `ψ_h` is any smooth loop profile whose
transport coefficients are those of the mollified periodized profile. -/
def AuxiliaryDerivativeVarianceInput : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (ell : Scales), Admissible P p ell α d → ∀ (N : ℕ+), 1 ≤ cltK N (ell N) →
      ∀ (ψh : Circle (loopMasterLength (ell N)) → ℝ)
        (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength (ell N))))),
        (∀ k : ℤ, coeff (loopMasterLength (ell N))
          ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
          transportCoeffs P (loopMasterLength (ell N))
            (mixedReg hρ N (ell N) ⟨periodizedProfile p (observationLength (ell N)),
              periodizedProfileL2 p (ell N)⟩) k) →
        let Q : Configuration N → ℝ := fun X =>
          fluctIntegral (fun u => deriv (loopMasterProfile (ell N) ψh hψh).val (u / (ell N).val)) N X.val
        ∃ hQ : MemLp Q 2 (gibbsMeasure P N),
          variance (gibbsMeasure P N) Q (hQ.integrable one_le_two) ≤
            ENNReal.ofReal (C * cltK N (ell N) ^ ε *
              (cltK N (ell N) ^ P.val.2 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α))))

end Riesz1.Internal

end
end
