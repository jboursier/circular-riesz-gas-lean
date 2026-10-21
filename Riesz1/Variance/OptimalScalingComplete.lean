/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.OptimalScalingFiniteness
public import Riesz1.ToMathlib.MollifierExistence

/-!
# Optimal variance from the two loop estimates

Theorem 2 and its uniform form, conditional on the two estimates
in `QuantitativeVarianceInput`. No main theorem is imported.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- The final proof works simultaneously for the original test and the
two convolution families. The microscopic transport is constructed from
its Fourier coefficients. No existence assumption is needed. -/
theorem optimalScaling_family_of_input
    (hAux : AuxiliaryVarianceReductionInput) (hLoop : VarAlVarianceInput)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (r : ℝ) (hr : 0 < r) (hrhalf : r < 1 / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) → ∀ (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        let V := variance (gibbsMeasure P N)
          (fluctuation ⟨v.val, (optimalScaling_profile_memLp v).integrable one_le_two⟩)
          (optimalScaling_fluctuation_integrable P N v)
        let σ := cltVariance P (ell N) ⟨(fun x => (v.val x : ℂ)), v.property⟩
        V < ⊤ ∧ σ < ⊤ ∧
        |V.toReal - cltK N (ell N) ^ P.val.2 * σ.toReal| ≤
          C * cltK N (ell N) ^ (max (2 * P.val.2 - 1) (2 * α) + ε) := by
  obtain ⟨A, hA, hred⟩ := hAux P p α d ρ hρ r hr hrhalf ε hε
  obtain ⟨B, hB, hloop⟩ := hLoop P p α d ρ hρ r hr hrhalf ε hε
  refine ⟨A * (B + 1), by positivity, fun ell hadm N hK v f hv => ?_⟩
  obtain ⟨ψ, hψ, htr⟩ := loopMaster_exists_transport_length P (loopMasterLength (ell N))
    (mixedRegCircle hρ N (ell N) f) (mixedRegCircle_contDiff hρ N (ell N) f)
  have hh : 0 < (cltK N (ell N))⁻¹ := inv_pos.mpr (cltK_pos N (ell N))
  have hh1 : (cltK N (ell N))⁻¹ ≤ 1 := (inv_le_one₀ (cltK_pos N (ell N))).mpr hK
  obtain ⟨hL, _, hV⟩ := hloop ell hadm N hK v f hv _ hh le_rfl hh1 ψ hψ htr
  have hR := hred ell hadm N hK v f hv ψ hψ htr hL
  refine ⟨optimalScaling_fluctuation_variance_finite P N v,
    optimalScaling_test_variance_finite P p ell α d hadm N hρ r v f hv, ?_⟩
  exact optimalScaling_combine hK le_rfl hA.le hB.le hR hV

/-- Theorem 2, with every assertion of the
statement. Only the two loop estimates remain conditional. -/
theorem quantitative_variance_of_input
    (_hBE : External.BakryEmery) (_hPL : External.PrekopaLeindler)
    (hAux : AuxiliaryVarianceReductionInput) (hLoop : VarAlVarianceInput) :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ∀ (p : Profile) (alpha : ℝ) (d : TestData),
      (∀ ell : Scales, Admissible P p ell alpha d →
        ModelWellDefined P ∧
        ∀ N, CircleSobolev ((1 - s) / 2) (fun x => (testAtScale p (ell N) x : ℂ)) ∧
          circleVariance P p (ell N) < ⊤) ∧
      (∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
        ∀ ell : Scales, Admissible P p ell alpha d → ∀ N : ℕ+,
          1 ≤ (N : ℝ) * (ell N).val →
            ∃ hF : Integrable (fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩) (gibbsMeasure P N),
            variance (gibbsMeasure P N) (fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩) hF < ⊤ ∧
            |(variance (gibbsMeasure P N) (fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩) hF).toReal -
              ((N : ℝ) * (ell N).val) ^ s * (circleVariance P p (ell N)).toReal| ≤
                C * ((N : ℝ) * (ell N).val) ^ (max (2 * s - 1) (2 * alpha) + eps)) ∧
      ((∃ ell : Scales, Admissible P p ell alpha d) → CompactProfile p →
        ∃ f0 : Lp ℂ 2 (volume : Measure ℝ),
          RepresentsZeroExtension p f0 ∧ LineSobolev ((1 - s) / 2) f0 ∧
          lineVariance P f0 < ⊤ ∧
          ∃ C1 : ℝ, 0 < C1 ∧ ∀ a : Scale,
            CircleSobolev ((1 - s) / 2) (fun x => (testAtScale p a x : ℂ)) ∧
            circleVariance P p a < ⊤ ∧
            |(circleVariance P p a).toReal - (lineVariance P f0).toReal| ≤ C1 * a.val ^ (2 - s)) := by
  intro beta s hbeta hs hs1
  dsimp only
  intro p alpha d
  refine ⟨?_, ?_, ?_⟩
  · intro ell hadm
    exact optimalScaling_circle_finiteness ⟨(beta, s), hbeta, hs, hs1⟩ p ell alpha d hadm
  · intro eps heps
    obtain ⟨ρ, hρ⟩ := exists_isMollifier
    obtain ⟨C, hC, hall⟩ := optimalScaling_family_of_input hAux hLoop
      ⟨(beta, s), hbeta, hs, hs1⟩ p alpha d ρ hρ (1 / 4)
      (by norm_num) (by norm_num) eps heps
    refine ⟨C, hC, fun ell hadm N hK => ?_⟩
    let v : Profile := ⟨testAtScale p (ell N), testAtScaleL2 p (ell N)⟩
    have htest : OptimalScalingTest p ell N hρ (1 / 4) v
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :=
      Or.inl ⟨rfl, rfl⟩
    obtain ⟨hV, _, hbound⟩ := hall ell hadm N hK v _ htest
    exact ⟨optimalScaling_fluctuation_integrable ⟨(beta, s), hbeta, hs, hs1⟩ N v, hV, hbound⟩
  · intro hex hp
    exact optimalScaling_compact_comparison ⟨(beta, s), hbeta, hs, hs1⟩ p alpha d hex hp

/-- The uniform form of Theorem 2, with the exact
interface, and a common constant for smoothing and difference. -/
theorem quantitative_variance_uniform_of_input
    (_hBE : External.BakryEmery) (_hPL : External.PrekopaLeindler)
    (hAux : AuxiliaryVarianceReductionInput) (hLoop : VarAlVarianceInput) :
    QuantitativeVarianceUniformConclusion := by
  intro P p α d ρ hρ r hr hrhalf ε hε
  obtain ⟨C, hC, hall⟩ := optimalScaling_family_of_input hAux hLoop
    P p α d ρ hρ r hr hrhalf ε hε
  refine ⟨C, hC, fun ell hadm t ht ht1 hcases N hK v hv => ?_⟩
  let ξ := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
    {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
  let g := loopMasterLengthTest (loopMasterLength (ell N))
    (cltRegCircle hρ (loopMasterLength (ell N)) ht ξ)
    (cltRegCircle_contDiff hρ (loopMasterLength (ell N)) ht ξ)
  rcases hv with hv | hv
  · exact hall ell hadm N hK v g
      (Or.inr ⟨t, ht, ht1, hcases, Or.inl ⟨funext hv, rfl⟩⟩)
  · exact hall ell hadm N hK v (subCircleL2 ξ g)
      (Or.inr ⟨t, ht, ht1, hcases, Or.inr ⟨hv, rfl⟩⟩)

end Riesz1.Internal

end
