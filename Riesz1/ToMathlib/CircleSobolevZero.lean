/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Riesz1.ToMathlib.Poincare.CircleProbability
public import Riesz1.ToMathlib.WeightedSobolev.Graph
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts

/-!
# Zero derivatives in the completed Sobolev graph on a circle

The rotation argument in Lemma 3.9: a function in the smooth periodic
graph completion with zero derivative is almost everywhere equal to its mean. The proof
passes the circle Poincaré inequality to the graph completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace Riesz1

theorem periodic_circleLift (T : ℝ) (f : AddCircle T → ℝ) :
    Function.Periodic (fun x : ℝ => f (x : AddCircle T)) T := by
  intro x
  simp only [AddCircle.coe_add_period]

theorem periodic_circleLift_deriv (T : ℝ) (f : AddCircle T → ℝ) :
    Function.Periodic (deriv (fun x : ℝ => f (x : AddCircle T))) T := by
  intro x
  rw [← deriv_comp_add_const]
  have he : (fun y : ℝ => f ((y + T : ℝ) : AddCircle T)) =
      (fun y : ℝ => f (y : AddCircle T)) := funext (periodic_circleLift T f)
  rw [he]

/-- Continuously differentiable real functions on the circle, certified on their lifts. -/
def CircleC1Function (T : ℝ) :=
  {f : AddCircle T → ℝ // ContDiff ℝ 1 (fun x : ℝ => f (x : AddCircle T))}

/-- The derivative of a continuously differentiable periodic lift, descended to the circle. -/
def circleLiftDerivative (T : ℝ) (f : CircleC1Function T) : AddCircle T → ℝ :=
  (periodic_circleLift_deriv T f.val).lift

theorem circleLiftDerivative_coe (T : ℝ) (f : CircleC1Function T) (x : ℝ) :
    circleLiftDerivative T f (x : AddCircle T) =
      deriv (fun y : ℝ => f.val (y : AddCircle T)) x :=
  Function.Periodic.lift_coe _ x

theorem continuous_circle_of_lift {T : ℝ} {f : AddCircle T → ℝ}
    (hf : Continuous (fun x : ℝ => f (x : AddCircle T))) : Continuous f :=
  (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples T)).continuous_iff.mpr hf

theorem circleLiftDerivative_continuous {T : ℝ} (f : CircleC1Function T) :
    Continuous (circleLiftDerivative T f) := by
  apply continuous_circle_of_lift
  simpa only [circleLiftDerivative_coe] using f.property.continuous_deriv (by norm_num)

/-- The usual circle estimate written entirely on the circle, including its derivative. -/
theorem circle_variance_le_derivative_energy (T : ℝ) [Fact (0 < T)]
    (f : CircleC1Function T) :
    (∫ x, (f.val x - ∫ y, f.val y ∂AddCircle.haarAddCircle) ^ 2 ∂AddCircle.haarAddCircle) ≤
      (T / (2 * Real.pi)) ^ 2 *
        ∫ x, (circleLiftDerivative T f x) ^ 2 ∂AddCircle.haarAddCircle := by
  have he : (∫ x, (circleLiftDerivative T f x) ^ 2 ∂AddCircle.haarAddCircle) =
      T⁻¹ * ∫ x in (0 : ℝ)..T, (deriv (fun y : ℝ => f.val (y : AddCircle T)) x) ^ 2 := by
    rw [AddCircle.integral_haarAddCircle,
      ← AddCircle.intervalIntegral_preimage T 0 (fun x => (circleLiftDerivative T f x) ^ 2),
      zero_add]
    simp only [circleLiftDerivative_coe, smul_eq_mul]
  rw [he]
  exact integral_sub_mean_sq_le_haarAddCircle T f.val f.property

/-- Zero derivative in the completed periodic graph implies constancy. This uses the
actual smooth graph and imposes no regularity on the limiting representative. -/
theorem circleGraphH1_eq_mean_of_derivative_zero (T : ℝ) [Fact (0 < T)]
    {F : AddCircle T → ℝ}
    (hF : WeightedSobolev.IsGraphH1 AddCircle.haarAddCircle
      (fun _ : CircleC1Function T => True)
      (fun f => f.val) (circleLiftDerivative T) F (fun _ => 0)) :
    F =ᵐ[AddCircle.haarAddCircle] fun _ => ∫ x, F x ∂AddCircle.haarAddCircle := by
  obtain ⟨hFm, _, φ, _, hv, hg⟩ := hF
  have hφm (k : ℕ) : MemLp (φ k).val 2 AddCircle.haarAddCircle :=
    (continuous_circle_of_lift (φ k).property.continuous).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hφgm (k : ℕ) : MemLp (circleLiftDerivative T (φ k)) 2 AddCircle.haarAddCircle :=
    (circleLiftDerivative_continuous (φ k)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hv' := WeightedSobolev.tendsto_integral_sq_of_lintegral
    (fun k => ((hφm k).sub hFm).aestronglyMeasurable) hv
  have hvar := WeightedSobolev.tendsto_integral_sub_mean_sq hFm hφm hv'
  have hg' := WeightedSobolev.tendsto_integral_sq_of_lintegral
    (fun k => ((hφgm k).sub (MemLp.zero')).aestronglyMeasurable) hg
  simp only [Pi.sub_apply, sub_zero] at hg'
  have hle := le_of_tendsto_of_tendsto' hvar
    (hg'.const_mul ((T / (2 * Real.pi)) ^ 2))
    (fun k => circle_variance_le_derivative_energy T (φ k))
  rw [mul_zero] at hle
  have hzero : (∫ x, (F x - ∫ y, F y ∂AddCircle.haarAddCircle) ^ 2
      ∂AddCircle.haarAddCircle) = 0 :=
    le_antisymm hle (integral_nonneg fun _ => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    ((hFm.sub (memLp_const _)).integrable_sq)).mp hzero
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- A completed circle observable with zero derivative has all exponential moments,
and the logarithmic moment generating function is exactly linear. This is the analytic
singleton case of Lemma 3.9. -/
theorem circleGraphH1_log_mgf_eq_of_derivative_zero (T : ℝ) [Fact (0 < T)]
    {F : AddCircle T → ℝ}
    (hF : WeightedSobolev.IsGraphH1 AddCircle.haarAddCircle
      (fun _ : CircleC1Function T => True)
      (fun f => f.val) (circleLiftDerivative T) F (fun _ => 0)) (t : ℝ) :
    Integrable F AddCircle.haarAddCircle ∧
      Integrable (fun x => Real.exp (t * F x)) AddCircle.haarAddCircle ∧
      Real.log (∫ x, Real.exp (t * F x) ∂AddCircle.haarAddCircle) =
        t * ∫ x, F x ∂AddCircle.haarAddCircle := by
  have hc := circleGraphH1_eq_mean_of_derivative_zero T hF
  have he : (fun x => Real.exp (t * F x)) =ᵐ[AddCircle.haarAddCircle]
      (fun _ => Real.exp (t * ∫ x, F x ∂AddCircle.haarAddCircle)) :=
    hc.mono fun x hx => congrArg (fun r => Real.exp (t * r)) hx
  refine ⟨hF.memLp_fun.integrable one_le_two, (integrable_const _).congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, Real.log_exp]

end Riesz1

end
