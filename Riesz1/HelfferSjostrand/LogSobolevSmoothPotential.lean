/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.BakryEmery
public import Riesz1.HelfferSjostrand.LogSobolevTransfer
public import Riesz1.ToMathlib.Herbst.Herbst

/-!
# Logarithmic Sobolev and Herbst bounds for smooth uniformly convex potentials

From the explicit Bakry–Émery hypothesis, the entropy inequality extends to bounded
C¹ tests with bounded gradient. The Herbst argument then gives the logarithmic
moment bound. This covers smooth whole-space potentials. The extension to arbitrary
convex conditioning and Borel log-concave densities is a separate step.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

namespace LogSobolevInternal

/-- Identifies the gradient energy used by the criterion with the derivative energy
used by the general Herbst argument. -/
lemma norm_gradient_eq_norm_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (q : E → ℝ) (x : E) :
    ‖gradient q x‖ = ‖fderiv ℝ q x‖ := by
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

end LogSobolevInternal

/-- The smooth criterion, extended to bounded C¹ tests for a smooth potential.
Normalization, probability, and all entropy and energy integrability are conclusions. -/
theorem logSobolev_smooth_potential_smooth (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    (V : EuclideanSpace ℝ (Fin d) → ℝ) (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h) :
    ∃ (_ : Integrable (fun x => Real.exp (-V x)) volume),
      0 < (∫ x, Real.exp (-V x)) ∧
      let ν : Measure (EuclideanSpace ℝ (Fin d)) :=
        volume.withDensity (fun x =>
          ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
      IsProbabilityMeasure ν ∧
        ∀ q : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 q →
          (∃ C, ∀ x, |q x| ≤ C) → (∃ D, ∀ x, ‖gradient q x‖ ≤ D) →
          ∃ (_ : Integrable (fun x => q x ^ 2) ν)
            (_ : Integrable (fun x => Real.negMulLog (q x ^ 2)) ν)
            (_ : Integrable (fun x => ‖gradient q x‖ ^ 2) ν),
            -(∫ x, Real.negMulLog (q x ^ 2) ∂ν) +
                Real.negMulLog (∫ x, q x ^ 2 ∂ν) ≤
              2 * w * ∫ x, ‖gradient q x‖ ^ 2 ∂ν := by
  obtain ⟨hi, hZ, hp, hLSI⟩ := hBE d hd w hw V hV hH
  let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x =>
    ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
  refine ⟨hi, hZ, hp, ?_⟩
  have : IsProbabilityMeasure ν := hp
  intro q hq ⟨C, hC⟩ ⟨D, hD⟩
  have hD' : ∀ x, ‖fderiv ℝ q x‖ ≤ D := by
    intro x
    rw [← LogSobolevInternal.norm_gradient_eq_norm_fderiv]
    exact hD x
  obtain ⟨hi₁, hi₂, hi₃⟩ := LogSobolevInternal.test_integrable (μ := ν) hq hC hD'
  simp_rw [← LogSobolevInternal.norm_gradient_eq_norm_fderiv] at hi₃
  refine ⟨hi₁, hi₂, hi₃, ?_⟩
  have h := LogSobolevInternal.lsi_of_smooth_tests (μ := ν) w
    (fun p hp' ⟨A, hA⟩ ⟨B, hB⟩ => ?_) hq hC hD'
  · simpa only [LogSobolevInternal.norm_gradient_eq_norm_fderiv] using h
  · have hpb : Bornology.IsBounded (range p) :=
      isBounded_iff_forall_norm_le.mpr ⟨A, by simpa only [forall_mem_range, Real.norm_eq_abs]⟩
    have hpd : Bornology.IsBounded (range (gradient p)) :=
      isBounded_iff_forall_norm_le.mpr ⟨B, by
        simpa only [forall_mem_range, LogSobolevInternal.norm_gradient_eq_norm_fderiv]⟩
    obtain ⟨_, _, _, he⟩ := hLSI p hp' hpb hpd
    simpa only [LogSobolevInternal.norm_gradient_eq_norm_fderiv] using he

/-- Herbst's estimate for a bounded C¹ observable with globally bounded gradient, under a
smooth whole-space uniformly convex potential. The only external hypothesis is `hBE`. -/
theorem logSobolev_herbst_smooth_potential (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    (V : EuclideanSpace ℝ (Fin d) → ℝ) (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h) :
    ∃ (_ : Integrable (fun x => Real.exp (-V x)) volume),
      0 < (∫ x, Real.exp (-V x)) ∧
      let ν : Measure (EuclideanSpace ℝ (Fin d)) :=
        volume.withDensity (fun x =>
          ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
      IsProbabilityMeasure ν ∧
        ∀ F : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 F →
          (∃ C, ∀ x, |F x| ≤ C) → ∀ L : ℝ, (∀ x, ‖gradient F x‖ ≤ L) → ∀ t : ℝ,
          Integrable F ν ∧ Integrable (fun x => Real.exp (t * F x)) ν ∧
            Real.log (∫ x, Real.exp (t * F x) ∂ν) ≤
              t * ∫ x, F x ∂ν + w / 2 * t ^ 2 * L ^ 2 := by
  obtain ⟨hi, hZ, hp, hLSI⟩ := logSobolev_smooth_potential_smooth hBE hd hw V hV hH
  refine ⟨hi, hZ, hp, ?_⟩
  have := hp
  intro F hF hFb L hL t
  obtain ⟨C, hC⟩ := hFb
  refine ⟨herbst_integrable_of_bounded hF.continuous hC,
    herbst_integrable_exp hF.continuous hC t, ?_⟩
  apply herbst_log_mgf_le _ w hw ?_ F hF ⟨C, hC⟩ L ?_ t
  · intro q hq hqb ⟨D, hD⟩
    have hD' : ∃ D, ∀ x, ‖gradient q x‖ ≤ D :=
      ⟨D, fun x => by rw [LogSobolevInternal.norm_gradient_eq_norm_fderiv]; exact hD x⟩
    obtain ⟨_, _, _, he⟩ := hLSI q hq hqb hD'
    simpa only [Real.negMulLog_eq_neg, integral_neg, neg_neg,
      LogSobolevInternal.norm_gradient_eq_norm_fderiv, sub_eq_add_neg] using he
  · intro x
    rw [← LogSobolevInternal.norm_gradient_eq_norm_fderiv]
    exact hL x

end Riesz1

end
