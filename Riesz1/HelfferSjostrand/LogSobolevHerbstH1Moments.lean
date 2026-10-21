/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevLogConcave
public import Riesz1.ToMathlib.Gaussian.AffineDensity
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Exponential moments of the conditioned log-concave Gaussian density

For `ν = c 1_Ω f γ` with `f` log-concave, the function `-log f` is convex on the interior of the
positive support. It therefore has an affine minorant there, so `f` is bounded by an exponential
of an affine function, and the support frontier is Lebesgue-null. The density of `ν` is thus
dominated by an affine Gaussian. Every exponential moment `∫ exp(s‖x‖) dν` is finite. These
moments justify the passage to the limit in the unbounded Herbst bound.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace Riesz1.LogSobolevInternal

/-- Completing the square: for `0 < w`, `s r - r²/(4w) ≤ w s²`. -/
lemma mul_sub_sq_div_le {w : ℝ} (hw : 0 < w) (s r : ℝ) :
    s * r - (4 * w)⁻¹ * r ^ 2 ≤ w * s ^ 2 := by
  have hw0 : w ≠ 0 := hw.ne'
  have h : 0 ≤ (r - 2 * w * s) ^ 2 / (4 * w) := by positivity
  have hexp : (r - 2 * w * s) ^ 2 / (4 * w) = (4 * w)⁻¹ * r ^ 2 - s * r + w * s ^ 2 := by
    field_simp
    ring
  linarith

/-- Multiplying `exp(s‖x‖)` into an affine Gaussian gives at most a constant times a Gaussian
with twice the variance. This is the pointwise step behind the exponential moments. -/
lemma exp_mul_norm_mul_gaussian_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w : ℝ} (hw : 0 < w) (s : ℝ) (a : E) (b : ℝ) (x : E) :
    Real.exp (s * ‖x‖) * Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2 + ⟪a, x⟫_ℝ + b)) ≤
      Real.exp (w * s ^ 2) * Real.exp (-((2 * (2 * w))⁻¹ * ‖x‖ ^ 2 + ⟪a, x⟫_ℝ + b)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hw0 : w ≠ 0 := hw.ne'
  have h := mul_sub_sq_div_le hw s ‖x‖
  have e : (2 * (2 * w))⁻¹ = (4 * w)⁻¹ := by
    congr 1
    ring
  have e' : (2 * w)⁻¹ = 2 * (4 * w)⁻¹ := by
    field_simp
    ring
  rw [e, e']
  linarith

/-- The conditioned density `c 1_Ω f γ` of `ν` has every exponential moment of `‖x‖` finite. -/
theorem integrable_exp_mul_norm {d : ℕ} {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    {c : ℝ} (hc : 0 < c) (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)))
    (s : ℝ) : Integrable (fun x => Real.exp (s * ‖x‖)) ν := by
  classical
  let r := Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2)))
  let S := {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}
  have hSc : Convex ℝ S := convex_positive_support hΩ hlog
  have hnull : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∉ frontier S :=
    ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hSc.addHaar_frontier volume)
  have hr0 : ∀ x, x ∉ S → r x = 0 := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · have hfz : f x = 0 := le_antisymm (not_lt.mp (fun hp => hx ⟨hxΩ, hp⟩)) (hf0 x hxΩ)
      simp [r, hxΩ, hfz]
    · simp [r, hxΩ]
  have hr_nonneg : ∀ x, 0 ≤ r x := by
    intro x
    by_cases hxΩ : x ∈ Ω
    · simp only [r, indicator_of_mem hxΩ]
      exact mul_nonneg (hf0 x hxΩ) (Real.exp_pos _).le
    · simp [r, hxΩ]
  -- The positive support has nonempty interior, since `ν` is a probability.
  have hSne : (interior S).Nonempty := by
    by_contra hne
    have hempty : interior S = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hrz : (fun x => ENNReal.ofReal (c * r x)) =ᵐ[volume] 0 := by
      filter_upwards [hnull] with x hx
      have hxS : x ∉ S := fun hs => hx ⟨subset_closure hs, by simp [hempty]⟩
      simp [hr0 x hxS]
    have hzero : ν = 0 := by
      rw [hν]
      exact (withDensity_congr_ae hrz).trans withDensity_zero
    have hone := measure_univ (μ := ν)
    rw [hzero] at hone
    norm_num at hone
  -- The affine minorant of `-log f` on the interior of the positive support.
  have hg : ConvexOn ℝ (interior S) (fun x => -Real.log (f x)) :=
    (convexOn_neg_log_positive_support hΩ hlog).subset interior_subset hSc.interior
  have hcont : ContinuousOn (fun x => -Real.log (f x)) (interior S) :=
    continuousOn_neg_log_positive_support hΩ hlog
  obtain ⟨l, b, hl⟩ := exists_affine_minorant_open isOpen_interior hSne hg hcont
  let a := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm l
  have hla : ∀ x, ⟪a, x⟫_ℝ = l x := fun x => InnerProductSpace.toDual_symm_apply
  -- Almost everywhere, `c r` is dominated by an affine Gaussian.
  have hdom : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      c * r x ≤ c * Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2 + ⟪a, x⟫_ℝ + b)) := by
    filter_upwards [hnull] with x hx
    by_cases hxI : x ∈ interior S
    · have hxS : x ∈ S := interior_subset hxI
      have hxΩ : x ∈ Ω := hxS.1
      have hfpos : 0 < f x := hxS.2
      have hfle : f x ≤ Real.exp (-(l x + b)) :=
        (Real.log_le_iff_le_exp hfpos).mp (by linarith [hl x hxI])
      have hrx : r x = f x * Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2)) := by
        simp only [r, indicator_of_mem hxΩ]
      have hsplit : -((2 * w)⁻¹ * ‖x‖ ^ 2 + ⟪a, x⟫_ℝ + b) =
          -(l x + b) + -((2 * w)⁻¹ * ‖x‖ ^ 2) := by
        rw [hla]
        ring
      rw [hrx, hsplit, Real.exp_add]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hfle (Real.exp_pos _).le) hc.le
    · have hxS : x ∉ S := fun hs => hx ⟨subset_closure hs, hxI⟩
      rw [hr0 x hxS, mul_zero]
      exact mul_nonneg hc.le (Real.exp_pos _).le
  -- Transfer the integrability from `ν` to the Lebesgue density.
  have hr_meas : Measurable r :=
    (hf.mul (by fun_prop)).indicator hΩm
  have hρ_meas : Measurable (fun x => ENNReal.ofReal (c * r x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hr_meas)
  have hρ_fin : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ENNReal.ofReal (c * r x) < ⊤ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hreal : ∀ x, (ENNReal.ofReal (c * r x)).toReal = c * r x := fun x =>
    ENNReal.toReal_ofReal (mul_nonneg hc.le (hr_nonneg x))
  rw [hν, integrable_withDensity_iff hρ_meas hρ_fin]
  simp only [hreal]
  -- The affine Gaussian majorant with doubled variance dominates the integrand a.e.
  have hG := (Gaussian.integrable_exp_quadratic_affine (E := EuclideanSpace ℝ (Fin d))
    (show (0 : ℝ) < 2 * w by positivity) a b).const_mul (Real.exp (w * s ^ 2) * c)
  refine Integrable.mono' hG
    ((Real.measurable_exp.comp (measurable_const.mul measurable_norm)).mul
      (measurable_const.mul hr_meas)).aestronglyMeasurable ?_
  filter_upwards [hdom] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg hc.le (hr_nonneg x)))]
  calc Real.exp (s * ‖x‖) * (c * r x)
      ≤ Real.exp (s * ‖x‖) * (c * Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2 + ⟪a, x⟫_ℝ + b))) :=
        mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
    _ = c * (Real.exp (s * ‖x‖) * Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2 + ⟪a, x⟫_ℝ + b))) := by ring
    _ ≤ c * (Real.exp (w * s ^ 2) * Real.exp (-((2 * (2 * w))⁻¹ * ‖x‖ ^ 2 + ⟪a, x⟫_ℝ + b))) :=
        mul_le_mul_of_nonneg_left (exp_mul_norm_mul_gaussian_le hw s a b x) hc.le
    _ = (Real.exp (w * s ^ 2) * c) *
        Real.exp (-((2 * (2 * w))⁻¹ * ‖x‖ ^ 2 + ⟪a, x⟫_ℝ + b)) := by ring

end Riesz1.LogSobolevInternal

end

end
