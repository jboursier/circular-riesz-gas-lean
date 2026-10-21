/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.NondegeneracyZero
public import Riesz1.ToMathlib.Mollifier.RegularizationSobolev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import all Riesz1.Variance.LoopMaster

/-!
# Macroscopic nondegeneracy of the regularized variance

The macroscopic positive-variance alternative of the nondegeneracy step in the proof of
Theorem 3. A single nonzero Fourier mode supplies a uniform
lower bound. Contraction of every mode supplies the upper bound.
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

lemma nondegeneracy_unit_variance_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {h : ℝ} (hh : 0 < h) (P : Parameters) (p : Profile) :
    cltVariance P ⟨1, by norm_num⟩
      ⟨(fun x => (cltRegCircle hρ unitLength hh ⟨p.val, p.property⟩ x : ℂ)),
        Internal.nondegeneracy_regCircle_memLp hρ unitLength hh ⟨p.val, p.property⟩⟩ ≤ circleVariance P p ⟨1, by norm_num⟩ := by
  unfold cltVariance circleVariance
  simp only [testAtScale, ite_true]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  unfold circleSobolevSq
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false, nondegeneracy_unit_lift_coeff, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    apply ENNReal.ofReal_le_ofReal
    have hm := mollifierFT_sq_le_one hρ.isCircleMollifier (h * k)
    have hw : 0 ≤ |(k : ℝ)| ^ (2 * ((1 - P.val.2) / 2)) *
        ‖fourierCoeff (fun x => (p.val x : ℂ)) k‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hm hw]

lemma nondegeneracy_exists_nonzero_coeff (p : Profile)
    (hp : ¬ ∃ c : ℝ, p.val =ᵐ[volume] fun _ => c) :
    ∃ k : ℤ, k ≠ 0 ∧ fourierCoeff (fun x => (p.val x : ℂ)) k ≠ 0 := by
  by_contra! hh
  apply hp
  have hzero : circleSobolevSq 1 ⟨(fun x => (p.val x : ℂ)), p.property⟩ = 0 := by
    unfold circleSobolevSq
    apply ENNReal.tsum_eq_zero.mpr
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk, hh k hk]
  obtain ⟨c, hc⟩ := (circleSobolevSq_eq_zero_iff 1 _).mp hzero
  exact ⟨c.re, hc.mono fun x hx => congrArg Complex.re hx⟩

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
  obtain ⟨k, hk, hpk⟩ := Internal.nondegeneracy_exists_nonzero_coeff p hp
  let A := (2 * Real.pi) ^ (1 - P.val.2) /
    (2 * P.val.1 * rieszConstant (parametersExponent P))
  have hA : 0 < A := by
    simpa only [Real.one_rpow, mul_one] using
      Internal.nondegeneracy_variance_prefactor_pos P ⟨1, by norm_num⟩
  let w := |(k : ℝ)| ^ (1 - P.val.2) *
    ‖fourierCoeff (fun x => (p.val x : ℂ)) k‖ ^ 2
  have hw : 0 < w := mul_pos
    (Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hk)) _)
    (sq_pos_of_pos (norm_pos_iff.mpr hpk))
  have hs := circleSobolev_of_unit_primitive_transportRegularity P η B hη hB p
    n marks α C₀ hα0 hα1 hC₀ hprim hreg
  have hfinite : circleVariance P p ⟨1, by norm_num⟩ < ⊤ := by
    unfold circleVariance
    simp only [testAtScale, ite_true]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.2
  let b := 1 / (4 * max 1 |(k : ℝ)|)
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : 0 < (2 - P.val.2) / (4 + P.val.2) :=
    div_pos (by linarith [P.property.2.2]) (by linarith [P.property.2.1])
  have hevent := (tendsto_rpow_neg_atTop hd).eventually (gt_mem_nhds hb)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨Real.sqrt (A * w / 4), Real.sqrt (circleVariance P p ⟨1, by norm_num⟩).toReal + 1,
    max T 1, Real.sqrt_pos.mpr (by positivity), by positivity,
    lt_of_lt_of_le one_pos (le_max_right _ _), fun N hN => ?_⟩
  let hh := cltDelta_pos P N ⟨1, by norm_num⟩
  let V := cltVariance P ⟨1, by norm_num⟩
    ⟨(fun x => (cltRegCircle hρ unitLength hh ⟨p.val, p.property⟩ x : ℂ)),
      Internal.nondegeneracy_regCircle_memLp hρ unitLength hh ⟨p.val, p.property⟩⟩
  have hVle : V ≤ circleVariance P p ⟨1, by norm_num⟩ :=
    Internal.nondegeneracy_unit_variance_le hρ hh P p
  have hVfin := hVle.trans_lt hfinite
  have hδb : cltDelta P N ⟨1, by norm_num⟩ < b := by
    simpa only [cltDelta, mul_one] using hT (N : ℝ) ((le_max_left _ _).trans hN)
  have hm : (1 / 2 : ℝ) ≤ mollifierFT ρ (cltDelta P N ⟨1, by norm_num⟩ * k) := by
    have hsmall : |cltDelta P N ⟨1, by norm_num⟩ * (k : ℝ)| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_pos hh]
      have h1 : cltDelta P N ⟨1, by norm_num⟩ * (4 * max 1 |(k : ℝ)|) < 1 :=
        (lt_div_iff₀ (by positivity)).mp hδb
      nlinarith [mul_le_mul_of_nonneg_left (le_max_right 1 |(k : ℝ)|) hh.le]
    have hbound := mollifierFT_one_sub_le hρ.isCircleMollifier
      (cltDelta P N ⟨1, by norm_num⟩ * k)
    have hsq : (cltDelta P N ⟨1, by norm_num⟩ * (k : ℝ)) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      nlinarith [sq_abs (cltDelta P N ⟨1, by norm_num⟩ * (k : ℝ)),
        abs_nonneg (cltDelta P N ⟨1, by norm_num⟩ * (k : ℝ))]
    nlinarith [min_le_left ((cltDelta P N ⟨1, by norm_num⟩ * (k : ℝ)) ^ 2) 1]
  have hmode : ENNReal.ofReal (w / 4) ≤
      circleSobolevSq ((1 - P.val.2) / 2)
        ⟨(fun x => (cltRegCircle hρ unitLength hh ⟨p.val, p.property⟩ x : ℂ)),
          Internal.nondegeneracy_regCircle_memLp hρ unitLength hh ⟨p.val, p.property⟩⟩ := by
    refine le_trans ?_ (ENNReal.le_tsum k)
    simp only [ite_eq_right hk, Internal.nondegeneracy_unit_lift_coeff,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    apply ENNReal.ofReal_le_ofReal
    have he : 2 * ((1 - P.val.2) / 2) = 1 - P.val.2 := by ring
    rw [he]
    change w / 4 ≤ |(k : ℝ)| ^ (1 - P.val.2) *
      (‖fourierCoeff (fun x => (p.val x : ℂ)) k‖ ^ 2 *
        mollifierFT ρ (cltDelta P N ⟨1, by norm_num⟩ * k) ^ 2)
    nlinarith [mul_le_mul_of_nonneg_left
      (show (1 / 4 : ℝ) ≤ mollifierFT ρ (cltDelta P N ⟨1, by norm_num⟩ * k) ^ 2 by nlinarith)
      hw.le]
  have hlow : ENNReal.ofReal (A * w / 4) ≤ V := by
    have he : ENNReal.ofReal (A * w / 4) = ENNReal.ofReal A * ENNReal.ofReal (w / 4) := by
      rw [← ENNReal.ofReal_mul hA.le]
      congr 1
      ring
    rw [he]
    dsimp only [V, cltVariance]
    simp only [Real.one_rpow, mul_one]
    exact mul_le_mul le_rfl hmode zero_le zero_le
  refine ⟨hVfin, ?_, ?_⟩
  · apply Real.sqrt_le_sqrt
    have ht := ENNReal.toReal_mono hVfin.ne hlow
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ A * w / 4 by positivity)] using ht
  · exact (Real.sqrt_le_sqrt (ENNReal.toReal_mono hfinite.ne hVle)).trans (by linarith)

end Riesz1
