/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroVarianceInput
public import Riesz1.CLT.ErrorTwoInput
public import Riesz1.Variance.QuantitativeVarianceInput
public import Riesz1.Frozen.TestAtScaleL2
public import Riesz1.Frozen.PeriodizedProfile
public import Riesz1.Frozen.PeriodizedProfileL2
public import Riesz1.Bridges.InputConsolidationRotation
public import Riesz1.ToMathlib.CircleSobolevZero
public import Riesz1.ToMathlib.VarianceLawTransfer
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Implications between the conditional input propositions

Several conditional results take as hypotheses different formulations of two results of the
paper, Lemma 5.2 and Proposition 5.9. This file proves the three implications between those
formulations:

* `regMicroAPrioriInput_of_aPrioriConclusion`: `APrioriConclusion → RegMicroAPrioriInput`. The
  input asks for a constant independent of the centre `c`, while the conclusion allows a constant
  depending on `c`. The centre is moved to the origin by translation of the observation circle
  (`map_plainSum_eq_map_translate`), which leaves the Gibbs law of the plain sum unchanged, so
  the constant of the conclusion at the origin serves every centre.
* `errorTwoAPrioriInput_of_aPrioriConclusion`: `APrioriConclusion → ErrorTwoAPrioriInput`. The two
  propositions are the same assertion, with the envelope and both sums written out.
* `errorTwoLoopVarianceInput_of_varAlVarianceInput`: `VarAlVarianceInput → ErrorTwoLoopVarianceInput`.
  The input carries an extra radius `r`, which is fixed at `1/4`. The optimal-scaling test is the
  first alternative: the actual test at scale `ℓ` and the periodized profile itself. The
  integrability and finiteness certificate of the input turns the real bound into the `ENNReal`
  bound of the target.

No hypothesis is weakened, and no proof step is added to a statement of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

/-- The cutoff majorant of radius two is the envelope of Lemma 5.2 with `R = 2`: the two
indicators close at the same point, and `1 / x = x⁻¹`. -/
theorem cutoffMajorant_eq_aPrioriEnvelope (s lam K t : ℝ) :
    Riesz1.cutoffMajorant s lam K t = aPrioriEnvelope s lam K 2 t := by
  simp only [Riesz1.cutoffMajorant, Riesz1.majorantNear, Riesz1.majorantFar, aPrioriEnvelope,
    one_div]

/-- `APrioriConclusion` gives `RegMicroAPrioriInput`. The conclusion allows its constant to depend
on the centre, so the proof fixes the centre at the origin, and translates an arbitrary centre to
the origin with the same Gibbs law of the plain sum. -/
theorem regMicroAPrioriInput_of_aPrioriConclusion (hA : APrioriConclusion) :
    RegMicroAPrioriInput := by
  intro P lam hlam ε hε
  obtain ⟨C, hC, hbound⟩ := hA P lam hlam ε hε 2 two_pos 0
  refine ⟨C, hC, fun N ℓ hN M hM c f hf hderiv => ?_⟩
  have hfcont : Continuous f := Riesz1.continuous_circle_of_lift hf.continuous
  -- The translate `z ↦ f (z + c)` has the lift `u ↦ f (u + c)`, which is smooth.
  have hfun : (fun u : ℝ => f ((u : Circle (observationLength ℓ)) +
      (c : Circle (observationLength ℓ)))) =
      fun u : ℝ => f ((u + c : ℝ) : Circle (observationLength ℓ)) := by
    funext u
    rw [AddCircle.coe_add]
  have hsmooth : ContDiff ℝ 1 (fun u : ℝ =>
      f ((u : Circle (observationLength ℓ)) + (c : Circle (observationLength ℓ)))) := by
    rw [hfun]
    exact hf.comp (contDiff_id.add contDiff_const)
  -- The derivative of the translate at `u` is the derivative of `f` at `u + c`, which the
  -- envelope of `f` controls with centre `c`. Re-centring at `0` gives the envelope at `u`.
  have hsderiv : ∀ u : ℝ, |deriv (fun t : ℝ =>
      f ((t : Circle (observationLength ℓ)) + (c : Circle (observationLength ℓ)))) u| ≤
      M * aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ.val) 2
        |centralRep (observationLength ℓ) ((u - 0 : ℝ) : Circle (observationLength ℓ))| := by
    intro u
    have hd : deriv (fun t : ℝ => f ((t + c : ℝ) : Circle (observationLength ℓ))) u =
        deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) (u + c) :=
      deriv_comp_add_const (fun t : ℝ => f (t : Circle (observationLength ℓ))) c u
    have h := hderiv (u + c)
    rw [add_sub_cancel_right, cutoffMajorant_eq_aPrioriEnvelope] at h
    rw [hfun, hd, sub_zero]
    exact h
  obtain ⟨-, hB⟩ := hbound N ℓ hN M hM (fun z => f (z + (c : Circle (observationLength ℓ))))
    hsmooth hsderiv
  obtain ⟨hBi, hBv⟩ := hB
  have hcont_c : Continuous fun z : Circle (observationLength ℓ) =>
      f (z + (c : Circle (observationLength ℓ))) :=
    hfcont.comp (continuous_id.add continuous_const)
  have hmeas := measurable_plainSum ℓ N hfcont.measurable
  have hmeasc := measurable_plainSum ℓ N hcont_c.measurable
  have hlaw := map_plainSum_eq_map_translate P N ℓ hfcont c
  have hFi : Integrable (plainSum ℓ N f) (gibbsMeasure P N) :=
    (integrable_iff_of_map_eq hmeas hmeasc hlaw).2 hBi
  exact ⟨hFi, (variance_eq_of_map_eq hmeas hmeasc hlaw hFi hBi).trans_le hBv⟩

/-- `APrioriConclusion` gives `ErrorTwoAPrioriInput`. The two propositions state the same
assertion. The envelope and the two sums are written out in the second one. -/
theorem errorTwoAPrioriInput_of_aPrioriConclusion (hA : APrioriConclusion) :
    ErrorTwoAPrioriInput := by
  intro P lam hlam ε hε R hR c
  exact hA P lam hlam ε hε R hR c

/-- `VarAlVarianceInput` gives `ErrorTwoLoopVarianceInput`. The input is uniform over the radius
`r ∈ (0, 1/2)` and over the optimal-scaling test. The target has neither. The radius is fixed at
`1/4`, and the test is the first alternative of `OptimalScalingTest`: the actual test at scale `ℓ`
and the periodized profile, with no regularization. The input's finiteness certificate turns its
real bound into the `ENNReal` bound of the target. -/
theorem errorTwoLoopVarianceInput_of_varAlVarianceInput (hV : VarAlVarianceInput) :
    ErrorTwoLoopVarianceInput := by
  intro P p α d ρ hρ ε hε
  obtain ⟨C, hC, hbound⟩ := hV P p α d ρ hρ (1 / 4) (by norm_num) (by norm_num) ε hε
  refine ⟨C, hC, fun ell hadm N h hh hN hlow hh1 ψ hψ hcoeff => ?_⟩
  have hOST : OptimalScalingTest p ell N hρ (1 / 4)
      ⟨testAtScale p (ell N), testAtScaleL2 p (ell N)⟩
      ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :=
    Or.inl ⟨rfl, rfl⟩
  obtain ⟨hL, hfin, hbd⟩ := hbound ell hadm N hN
    ⟨testAtScale p (ell N), testAtScaleL2 p (ell N)⟩
    ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
    hOST h hh hlow hh1 ψ hψ hcoeff
  refine ⟨hL, (ENNReal.le_ofReal_iff_toReal_le hfin.ne ?_).2 hbd⟩
  exact mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hN) _)

end Riesz1.Internal

end
end
