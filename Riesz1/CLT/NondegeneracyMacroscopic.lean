/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.NondegeneracyZero
public import Riesz1.Variance.RegUniformMacroscopic
public import Riesz1.ToMathlib.CircleSobolevTriangle
public import Riesz1.ToMathlib.CircleSobolevTwoTerm
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import all Riesz1.ToMathlib.Mollifier.RegularizationSobolev
import all Riesz1.Variance.LoopMaster

/-!
# Macroscopic nondegeneracy of the regularized variance

The macroscopic positive-variance alternative of the nondegeneracy step in the proof of
Theorem 3. The fixed unregularized standard deviation is positive. The Sobolev
smoothing error and the reverse triangle inequality give uniform positive lower
and finite upper bounds for the regularized standard deviation.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz1
namespace Internal

lemma nondegeneracy_regCircle_memLp {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (L : Length) {h : ℝ} (hh : 0 < h)
    (ξ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) :
    MemLp (fun x => (cltRegCircle hρ L hh ξ x : ℂ)) 2 (arclength L) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hc : Continuous (cltRegCircle hρ L hh ξ) :=
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L.val)).continuous_iff.mpr
      (cltRegCircle_contDiff hρ L hh ξ).continuous
  change MemLp _ 2 volume
  exact (Complex.continuous_ofReal.comp hc).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)


lemma nondegeneracy_unit_lift_coe {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {h : ℝ} (hh : 0 < h) (p : Profile) (x : ℝ) :
    cltRegCircle hρ unitLength hh ⟨p.val, p.property⟩ (x : UnitAddCircle) =
      circleMollify ρ 1 h (fun t : ℝ => p.val (t : UnitAddCircle)) x := by
  exact cltRegCircle_coe hρ unitLength hh ⟨p.val, p.property⟩ x

lemma nondegeneracy_unit_lift_coeff {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {h : ℝ} (hh : 0 < h) (p : Profile) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (cltRegCircle hρ unitLength hh
      ⟨p.val, p.property⟩ x : ℂ)) k =
        fourierCoeff (fun x => (p.val x : ℂ)) k * (mollifierFT ρ (h * k) : ℂ) := by
  have : Fact (0 < unitLength.val) := ⟨unitLength.property⟩
  have hloc := locallyIntegrable_circle_lift (complexL2Integrable unitLength _ p.property).re
  simpa only [div_one] using fourierCoeff_circleMollify hρ hh hloc
    (show Function.Periodic (fun t : ℝ => p.val (t : UnitAddCircle)) 1 from
      fun t => by simp only [AddCircle.coe_add_period]) p.val
    (cltRegCircle hρ unitLength hh ⟨p.val, p.property⟩) (fun _ => rfl)
    (nondegeneracy_unit_lift_coe hρ hh p) k

/-- The reverse triangle inequality transfers a small Sobolev error to the
standard deviations. Finiteness of the original and the difference also gives
finiteness of the second profile. -/
lemma nondegeneracy_unit_variance_comparison (P : Parameters)
    (f g : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
    (hf : cltVariance P ⟨1, by norm_num⟩ f < ⊤)
    (he : cltVariance P ⟨1, by norm_num⟩ (subL2 f g) < ⊤) :
    cltVariance P ⟨1, by norm_num⟩ g < ⊤ ∧
      |Real.sqrt (cltVariance P ⟨1, by norm_num⟩ f).toReal -
        Real.sqrt (cltVariance P ⟨1, by norm_num⟩ g).toReal| ≤
          Real.sqrt (cltVariance P ⟨1, by norm_num⟩ (subL2 f g)).toReal := by
  let A := (2 * Real.pi) ^ (1 - P.val.2) /
    (2 * P.val.1 * rieszConstant (parametersExponent P))
  have hA : 0 < A := by
    simpa only [Real.one_rpow, mul_one] using
      nondegeneracy_variance_prefactor_pos P ⟨1, by norm_num⟩
  have hvar (u : {u : UnitAddCircle → ℂ // MemLp u 2 volume}) :
      cltVariance P ⟨1, by norm_num⟩ u =
        ENNReal.ofReal A * circleSobolevSq ((1 - P.val.2) / 2) u := by
    simp only [cltVariance, Real.one_rpow, mul_one, A]
  have hfin (u : {u : UnitAddCircle → ℂ // MemLp u 2 volume})
      (hu : cltVariance P ⟨1, by norm_num⟩ u < ⊤) :
      circleSobolevSq ((1 - P.val.2) / 2) u ≠ ⊤ := by
    intro htop
    rw [hvar, htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hA).ne'] at hu
    exact hu.false
  have hSf := hfin f hf
  have hSe := hfin (subL2 f g) he
  have hsub : circleSobolevSq ((1 - P.val.2) / 2) (subL2 g f) =
      circleSobolevSq ((1 - P.val.2) / 2) (subL2 f g) := by
    unfold circleSobolevSq
    apply tsum_congr
    intro k
    simp only [fourierCoeff_subL2, norm_sub_rev]
  have hSg : circleSobolevSq ((1 - P.val.2) / 2) g ≠ ⊤ := by
    have hb := circleSobolevSq_le_two_mul_add ((1 - P.val.2) / 2) g f
    rw [hsub] at hb
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨hSf, hSe⟩)) hb
  refine ⟨?_, ?_⟩
  · rw [hvar]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hSg)
  · simp only [hvar, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA.le,
      Real.sqrt_mul hA.le, ← mul_sub, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg A)]
    exact mul_le_mul_of_nonneg_left
      (circleSobolevSq_sqrt_sub_le ((1 - P.val.2) / 2) f g hSf hSg hSe)
      (Real.sqrt_nonneg A)

end Internal

/-- The positive macroscopic alternative of the nondegeneracy step in the proof of Theorem 3.
The constants precede the particle number. The hypotheses are the fixed
profile data (A1)--(A3), and the nonconstant alternative in the paper.
The variance is evaluated on the regularized profile. -/
theorem clt_nondegeneracy_macroscopic (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (hp : ¬ ∃ c : ℝ, p.val =ᵐ[volume] fun _ => c)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ c C K₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < K₀ ∧
      ∀ N : ℕ+, K₀ ≤ (N : ℝ) →
        let hh := cltDelta_pos P N ⟨1, by norm_num⟩
        let V := cltVariance P ⟨1, by norm_num⟩
          ⟨(fun x => (cltRegCircle hρ unitLength hh ⟨p.val, p.property⟩ x : ℂ)),
            Internal.nondegeneracy_regCircle_memLp hρ unitLength hh ⟨p.val, p.property⟩⟩
        V < ⊤ ∧ c ≤ Real.sqrt V.toReal ∧ Real.sqrt V.toReal ≤ C := by
  have hs := circleSobolev_of_unit_primitive_transportRegularity P η B hη hB p
    n marks α C₀ hα0 hα1 hC₀ hprim hreg
  have hfinite : circleVariance P p ⟨1, by norm_num⟩ < ⊤ := by
    unfold circleVariance
    simp only [testAtScale, ite_true]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.2
  let σ := Real.sqrt (circleVariance P p ⟨1, by norm_num⟩).toReal
  have hσ : 0 < σ := Real.sqrt_pos.mpr (ENNReal.toReal_pos
    (fun hz => hp ((clt_nondegeneracy_macroscopic_zero P p).mp hz)) hfinite.ne)
  let τ := (P.val.2 / 2 - α) / 2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hr : 0 < P.val.2 / 2 - α - τ := by dsimp [τ]; linarith
  obtain ⟨D, -, herror⟩ := regUniform_variance_macroscopic P p η B n marks α C₀ τ
    hη hB hC₀ hα0 hα1 hτ hprim hreg ρ hρ
  have hd : 0 < (2 - P.val.2) / (4 + P.val.2) :=
    div_pos (by linarith [P.property.2.2]) (by linarith [P.property.2.1])
  have hdecay : Tendsto (fun K : ℝ => D *
      (K ^ (-((2 - P.val.2) / (4 + P.val.2)))) ^ (P.val.2 / 2 - α - τ))
      atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop hd).rpow_const (p := P.val.2 / 2 - α - τ)
      (Or.inr hr.le)
    simpa only [Real.zero_rpow hr.ne', mul_zero] using hh.const_mul D
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hdecay.eventually (gt_mem_nhds (half_pos hσ)))
  refine ⟨σ / 2, σ + σ / 2, max T 1, half_pos hσ, by linarith,
    lt_of_lt_of_le one_pos (le_max_right _ _), fun N hN => ?_⟩
  let hh := cltDelta_pos P N ⟨1, by norm_num⟩
  have hδ1 : cltDelta P N ⟨1, by norm_num⟩ ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
      (show 1 ≤ (N : ℝ) * 1 by simpa only [mul_one] using (le_max_right T 1).trans hN)
      (neg_nonpos.mpr hd.le)
  obtain ⟨g, e, _, hg, he, hefin, hebound⟩ := herror _ hh hδ1
  have hgeq : g.val = cltRegCircle hρ unitLength hh ⟨p.val, p.property⟩ := by
    funext y
    induction y using QuotientAddGroup.induction_on with
    | H x => rw [hg, Internal.nondegeneracy_unit_lift_coe]
  let f : {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
    ⟨(fun x => (p.val x : ℂ)), p.property⟩
  let g' : {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
    ⟨(fun x => (g.val x : ℂ)), g.property⟩
  have heq : subL2 f g' = ⟨(fun x => (e.val x : ℂ)), e.property⟩ := by
    apply Subtype.ext
    funext x
    simp only [subL2, f, g', he, Complex.ofReal_sub]
  have hunit (q : Profile) : cltVariance P ⟨1, by norm_num⟩
      ⟨(fun x => (q.val x : ℂ)), q.property⟩ = circleVariance P q ⟨1, by norm_num⟩ := by
    simp only [cltVariance, circleVariance, testAtScale, ite_true]
  have hcomp := Internal.nondegeneracy_unit_variance_comparison P f g'
    (by rw [hunit]; exact hfinite) (by rw [heq, hunit]; exact hefin)
  have hsmall : Real.sqrt (circleVariance P e ⟨1, by norm_num⟩).toReal ≤ σ / 2 := by
    refine hebound.trans (le_of_lt ?_)
    simpa only [cltDelta, mul_one] using hT (N : ℝ) ((le_max_left _ _).trans hN)
  have hdiff : |σ - Real.sqrt (cltVariance P ⟨1, by norm_num⟩ g').toReal| ≤ σ / 2 := by
    have hc := hcomp.2
    rw [heq, hunit p, hunit e] at hc
    exact hc.trans hsmall
  have hb := abs_le.mp hdiff
  have hbounds : cltVariance P ⟨1, by norm_num⟩ g' < ⊤ ∧
      σ / 2 ≤ Real.sqrt (cltVariance P ⟨1, by norm_num⟩ g').toReal ∧
      Real.sqrt (cltVariance P ⟨1, by norm_num⟩ g').toReal ≤ σ + σ / 2 :=
    ⟨hcomp.1, by linarith [hb.2], by linarith [hb.1]⟩
  simpa only [g', hgeq] using hbounds

end Riesz1
