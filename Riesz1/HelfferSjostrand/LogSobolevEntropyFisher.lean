/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevEntropyH1
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Entropy–Fisher inequality for the conditioned Gaussian

Let `ν = f γ_Ω^w` be the probability of the conditioning theorems. This file proves the
first display of Lemma 3.8: for every probability `ρ` on the ambient space, the relative
entropy and the Fisher information satisfy

`Ent(ρ | ν) ≤ (w/2) Fisher(ρ | ν) ≤ 2w Fisher(ρ | ν)`.

The relative entropy is Mathlib's Kullback–Leibler divergence `InformationTheory.klDiv ρ ν`. It
equals `∫ f log f dν` when `ρ = f ν` and `+∞` otherwise. The Fisher information
is `4 ∫ |∇√f|² dν` for `f = dρ/dν`, where `∇√f` is the weak gradient of `√f` in the weighted
`H¹` space of `ν` over a set `U`. The gradient enters as the infimum over all
admissible gradients, which avoids choosing one. The inequality holds for every such `U` with
`ν`-almost every point in `closure U`. The only external hypothesis is `hBE`, the Bakry–Émery
criterion `External.BakryEmery`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1.LogSobolevEntropy

open scoped Classical in
/-- The Fisher information of a probability `ρ` relative to `ν`, over the weighted `H¹` space
`IsWeightedH1 ν U`. For `f = dρ/dν` it is `4 ∫ ‖G‖² dν`, minimised over all weak gradients `G` of
`√f`, and it is `+∞` when `ρ` is not absolutely continuous with respect to `ν` or when `√f` has no
weak gradient in `H¹(ν)`. -/
@[expose]
def fisherInfo {d : ℕ} (ν ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (U : Set (EuclideanSpace ℝ (Fin d))) : ENNReal :=
  if ρ ≪ ν then
    ⨅ (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (_ : WeightedSobolev.IsWeightedH1 ν U (fun x => Real.sqrt (ρ.rnDeriv ν x).toReal) G),
      4 * ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν
  else ⊤

/-- **Entropy–Fisher inequality** (first display of Lemma 3.8). Let `ν = f γ_Ω^w` be the
probability of the conditioning theorems, and let `U` satisfy `x ∈ closure U` for
`ν`-almost every `x`. For every probability `ρ`, the relative entropy is at most `(w/2)` times the
Fisher information, and this is at most `2w` times the Fisher information. -/
theorem klDiv_le_fisherInfo (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    (hΩpos : 0 < ∫ x in Ω, Real.exp (-((2*w)⁻¹ * ‖x‖^2)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = ((volume.restrict Ω).withDensity (fun x => ENNReal.ofReal
      (Real.exp (-((2*w)⁻¹ * ‖x‖^2)) / ∫ y in Ω, Real.exp (-((2*w)⁻¹ * ‖y‖^2))))).withDensity
      (fun x => ENNReal.ofReal (f x)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : ∀ᵐ x ∂ν, x ∈ closure U)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ] :
    InformationTheory.klDiv ρ ν ≤ ENNReal.ofReal (w / 2) * fisherInfo ν ρ U ∧
      ENNReal.ofReal (w / 2) * fisherInfo ν ρ U ≤ ENNReal.ofReal (2 * w) * fisherInfo ν ρ U := by
  have hc0 : ENNReal.ofReal (w / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  refine ⟨?_, mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) zero_le⟩
  by_cases hac : ρ ≪ ν
  swap
  · simp only [InformationTheory.klDiv_of_not_ac hac, fisherInfo, hac, ↓reduceIte,
      ENNReal.mul_top hc0]
    exact le_rfl
  -- the square of the square root of the density is the density
  set q : EuclideanSpace ℝ (Fin d) → ℝ := fun x => Real.sqrt (ρ.rnDeriv ν x).toReal with hq
  have hq2 : ∀ x, q x ^ 2 = (ρ.rnDeriv ν x).toReal := fun x => Real.sq_sqrt ENNReal.toReal_nonneg
  have hmass : ∫ x, (ρ.rnDeriv ν x).toReal ∂ν = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac]
    simp [measureReal_def]
  have hνmass : ν.real Set.univ = 1 := by simp [measureReal_def]
  -- the entropy bound for every admissible gradient
  have key : ∀ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      WeightedSobolev.IsWeightedH1 ν U q G →
        InformationTheory.klDiv ρ ν ≤ ENNReal.ofReal (w / 2) * (4 * ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν) := by
    intro G hG
    obtain ⟨hint, hintneg, -, hineq⟩ :=
      logSobolev_conditioning_H1 hBE hd hw hΩ hΩm hΩpos hf hf0 hlog ν hν hU hG
    simp only [hq2] at hint hintneg hineq
    rw [hmass, Real.negMulLog_one, add_zero] at hineq
    -- the relative entropy is the integral of `klFun` of the density
    have hklFun_int : Integrable (fun x => InformationTheory.klFun (ρ.rnDeriv ν x).toReal) ν := by
      have h1 : Integrable (fun x => -Real.negMulLog (ρ.rnDeriv ν x).toReal + 1 -
          (ρ.rnDeriv ν x).toReal) ν :=
        ((hintneg.neg).add (integrable_const 1)).sub hint
      refine h1.congr (Eventually.of_forall fun x => ?_)
      simp [InformationTheory.klFun, Real.negMulLog]
    have hint_klFun : ∫ x, InformationTheory.klFun (ρ.rnDeriv ν x).toReal ∂ν ≤
        2 * w * ∫ x, ‖G x‖ ^ 2 ∂ν := by
      have ia : Integrable (fun x => -Real.negMulLog (ρ.rnDeriv ν x).toReal + 1) ν :=
        (hintneg.neg).add (integrable_const 1)
      have e : ∫ x, InformationTheory.klFun (ρ.rnDeriv ν x).toReal ∂ν =
          ∫ x, (-Real.negMulLog (ρ.rnDeriv ν x).toReal + 1 - (ρ.rnDeriv ν x).toReal) ∂ν :=
        integral_congr_ae (Eventually.of_forall fun x => by simp [InformationTheory.klFun, Real.negMulLog])
      have ib : Integrable (fun x => -Real.negMulLog (ρ.rnDeriv ν x).toReal) ν := hintneg.neg
      rw [e, integral_sub ia hint, integral_add ib (integrable_const 1), integral_neg,
        integral_const, hmass, hνmass]
      simp only [smul_eq_mul, mul_one]
      linarith
    -- the relative entropy as an extended-real integral
    have hklDiv : InformationTheory.klDiv ρ ν =
        ENNReal.ofReal (∫ x, InformationTheory.klFun (ρ.rnDeriv ν x).toReal ∂ν) := by
      rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac,
        ← ofReal_integral_eq_lintegral_ofReal hklFun_int
          (Eventually.of_forall fun x => InformationTheory.klFun_nonneg ENNReal.toReal_nonneg)]
    -- the squared `L²` norm of `G`, in extended-real form
    have hGlin : ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, ‖G x‖ ^ 2 ∂ν) := by
      rw [WeightedSobolev.integral_norm_sq_eq_toReal_lintegral hG.memLp_grad.aestronglyMeasurable,
        ENNReal.ofReal_toReal (WeightedSobolev.lintegral_enorm_sq_ne_top_of_memLp hG.memLp_grad)]
    have h4 : (4 : ENNReal) * ENNReal.ofReal (∫ x, ‖G x‖ ^ 2 ∂ν) =
        ENNReal.ofReal (4 * ∫ x, ‖G x‖ ^ 2 ∂ν) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [hklDiv, hGlin, h4, ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hint_klFun])
  -- minimise over all admissible gradients
  simp only [fisherInfo, hac, ↓reduceIte]
  refine le_trans ?_ (le_of_eq (ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top).symm)
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  exact le_iInf fun hG => key G hG

end Riesz1.LogSobolevEntropy

end

end
