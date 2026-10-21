/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HeatKernel.OperatorsSingular
public import Riesz1.Kernel.PeriodicZeta

/-!
# The mean-zero primitive of a smooth circle function

For a smooth real function `ξ` on the unit circle with mean `m = ∫_0^1 ξ`, the primitive
`Ξ(t) = ∫_0^t (ξ(u) - m) du` is smooth on `ℝ`, periodic with period one, and Lipschitz.
Its circle version has Fourier coefficients `ξ̂(k) = 2πik Ξ̂(k)` for `k ≠ 0`.

This file supplies the regularity facts used by the pointwise transport formula.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- The mean of a real function on the unit circle, as its integral over one period. -/
noncomputable def circleMean (ξ : UnitAddCircle → ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, ξ (u : UnitAddCircle)

/-- The mean-zero primitive `Ξ(t) = ∫_0^t (ξ(u) - m) du` of a real function on the circle. -/
noncomputable def meanZeroPrimitive (ξ : UnitAddCircle → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, (ξ (u : UnitAddCircle) - circleMean ξ)

section Primitive

variable {ξ : UnitAddCircle → ℝ}

lemma continuous_lift (hξ : IsSmoothCircle ξ) : Continuous fun u : ℝ => ξ (u : UnitAddCircle) :=
  (show ContDiff ℝ ∞ (fun u : ℝ => ξ (u : UnitAddCircle)) from hξ).continuous

lemma continuous_centered (hξ : IsSmoothCircle ξ) :
    Continuous fun u : ℝ => ξ (u : UnitAddCircle) - circleMean ξ :=
  (continuous_lift hξ).sub continuous_const

lemma meanZeroPrimitive_hasDerivAt (hξ : IsSmoothCircle ξ) (t : ℝ) :
    HasDerivAt (meanZeroPrimitive ξ) (ξ (t : UnitAddCircle) - circleMean ξ) t :=
  ((continuous_centered hξ).integral_hasStrictDerivAt 0 t).hasDerivAt

lemma integral_centered_eq_zero (hξ : IsSmoothCircle ξ) :
    ∫ u in (0 : ℝ)..1, (ξ (u : UnitAddCircle) - circleMean ξ) = 0 := by
  rw [intervalIntegral.integral_sub ((continuous_lift hξ).intervalIntegrable 0 1)
    intervalIntegrable_const, intervalIntegral.integral_const]
  simp [circleMean]

lemma centered_periodic (ξ : UnitAddCircle → ℝ) :
    Function.Periodic (fun u : ℝ => ξ (u : UnitAddCircle) - circleMean ξ) 1 := by
  intro u
  simp only [AddCircle.coe_add_period]

lemma meanZeroPrimitive_periodic (hξ : IsSmoothCircle ξ) :
    Function.Periodic (meanZeroPrimitive ξ) 1 := by
  intro t
  unfold meanZeroPrimitive
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => ξ (u : UnitAddCircle) - circleMean ξ)
      volume a b := fun a b => (continuous_centered hξ).intervalIntegrable a b
  rw [← sub_eq_zero, intervalIntegral.integral_interval_sub_left (hint 0 (t + 1)) (hint 0 t)]
  rw [(centered_periodic ξ).intervalIntegral_add_eq t 0, zero_add, integral_centered_eq_zero hξ]

lemma meanZeroPrimitive_one (hξ : IsSmoothCircle ξ) :
    meanZeroPrimitive ξ 1 = meanZeroPrimitive ξ 0 := by
  simpa using meanZeroPrimitive_periodic hξ 0

lemma contDiff_meanZeroPrimitive (hξ : IsSmoothCircle ξ) :
    ContDiff ℝ ∞ (meanZeroPrimitive ξ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (meanZeroPrimitive_hasDerivAt hξ t).differentiableAt, ?_⟩
  have hd : deriv (meanZeroPrimitive ξ) = fun t : ℝ => ξ (t : UnitAddCircle) - circleMean ξ :=
    funext fun t => (meanZeroPrimitive_hasDerivAt hξ t).deriv
  rw [hd]
  exact (show ContDiff ℝ ∞ (fun u : ℝ => ξ (u : UnitAddCircle)) from hξ).sub contDiff_const

/-- A smooth function on the unit circle has a uniform bound on its centered lift. -/
lemma exists_bound_centered (hξ : IsSmoothCircle ξ) :
    ∃ M : ℝ, ∀ u : ℝ, |ξ (u : UnitAddCircle) - circleMean ξ| ≤ M := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
    ((centered_periodic ξ).isBounded_of_continuous one_ne_zero (continuous_centered hξ))
  exact ⟨C, fun u => by simpa using hC _ ⟨u, rfl⟩⟩

/-- A function with derivative bounded by `M` is `M`-Lipschitz on `ℝ`. -/
lemma abs_sub_le_of_hasDerivAt_bound {f f' : ℝ → ℝ} {M : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hM : ∀ t, |f' t| ≤ M) (a b : ℝ) : |f a - f b| ≤ M * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (f := f) (f' := f')
    (s := univ) (C := M) (fun t _ => (hf t).hasDerivWithinAt)
    (fun t _ => by simpa using hM t) convex_univ (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

/-- The primitive is `M`-Lipschitz, where `M` bounds the centered function. -/
lemma abs_meanZeroPrimitive_sub_le (hξ : IsSmoothCircle ξ) {M : ℝ}
    (hM : ∀ u : ℝ, |ξ (u : UnitAddCircle) - circleMean ξ| ≤ M) (a b : ℝ) :
    |meanZeroPrimitive ξ a - meanZeroPrimitive ξ b| ≤ M * |a - b| :=
  abs_sub_le_of_hasDerivAt_bound (fun t => meanZeroPrimitive_hasDerivAt hξ t) hM a b

/-- The circle version of the primitive, lifted from its periodic real version. -/
noncomputable def circlePrimitive (hξ : IsSmoothCircle ξ) : UnitAddCircle → ℝ :=
  (meanZeroPrimitive_periodic hξ).lift

lemma circlePrimitive_coe (hξ : IsSmoothCircle ξ) (t : ℝ) :
    circlePrimitive hξ (t : UnitAddCircle) = meanZeroPrimitive ξ t :=
  (meanZeroPrimitive_periodic hξ).lift_coe t

lemma isSmoothCircle_circlePrimitive (hξ : IsSmoothCircle ξ) :
    IsSmoothCircle (circlePrimitive hξ) := by
  unfold IsSmoothCircle
  have : (fun t : ℝ => circlePrimitive hξ (t : UnitAddCircle)) = meanZeroPrimitive ξ :=
    funext (circlePrimitive_coe hξ)
  rw [this]
  exact contDiff_meanZeroPrimitive hξ

/-- The character `e^{2πi(-k)x}` takes the value one at the integer endpoint `1`. -/
lemma exp_char_one (k : ℤ) :
    Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
  rw [show 2 * π * I * ((-k : ℤ) : ℂ) * ((1 : ℝ) : ℂ) = ((-k : ℤ) : ℂ) * (2 * π * I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- The integral of the character `e^{2πi(-k)x}` over one period vanishes for `k ≠ 0`. -/
lemma integral_fourier_char_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) = 0 := by
  have hk' : ((-k : ℤ) : ℂ) ≠ 0 := by exact_mod_cast neg_ne_zero.2 hk
  have hc : (2 * π * I * ((-k : ℤ) : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hk]
  rw [integral_exp_mul_complex hc, exp_char_one k]
  simp

/-- The Fourier coefficients of the primitive: `ξ̂(k) = 2πik Ξ̂(k)` for `k ≠ 0`. -/
lemma circleCoeff_eq_mul_primitive (hξ : IsSmoothCircle ξ) {k : ℤ} (hk : k ≠ 0) :
    circleCoeff ξ k = (2 * π * I * (k : ℂ)) * circleCoeff (circlePrimitive hξ) k := by
  set c : ℂ := 2 * π * I * ((-k : ℤ) : ℂ) with hc_def
  set E : ℝ → ℂ := fun x => Complex.exp (c * (x : ℂ)) with hE
  have hEd : ∀ x : ℝ, HasDerivAt E (c * E x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c)
    simpa [hE, mul_comm] using h1.cexp
  have hG : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ((meanZeroPrimitive ξ y : ℝ) : ℂ))
      (((ξ (x : UnitAddCircle) - circleMean ξ : ℝ) : ℂ)) x :=
    fun x => (meanZeroPrimitive_hasDerivAt hξ x).ofReal_comp
  have hEcont : Continuous E := by
    simp only [hE]; fun_prop
  have hcontc : Continuous fun x : ℝ => ((ξ (x : UnitAddCircle) - circleMean ξ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_centered hξ)
  have hcontξ : Continuous fun x : ℝ => ((ξ (x : UnitAddCircle) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_lift hξ)
  have hEξ : IntervalIntegrable (fun x : ℝ => E x * ((ξ (x : UnitAddCircle) : ℝ) : ℂ)) volume 0 1 :=
    (hEcont.mul hcontξ).intervalIntegrable 0 1
  have hcEm : IntervalIntegrable (fun x : ℝ => (circleMean ξ : ℂ) * E x) volume 0 1 :=
    ((hEcont.const_mul _)).intervalIntegrable 0 1
  -- Integration by parts for `E · Ξ'`. The boundary terms cancel by periodicity.
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
    (u := E) (u' := fun x => c * E x)
    (v := fun y : ℝ => ((meanZeroPrimitive ξ y : ℝ) : ℂ))
    (v' := fun x => ((ξ (x : UnitAddCircle) - circleMean ξ : ℝ) : ℂ))
    (fun x _ => hEd x) (fun x _ => hG x)
    ((hEcont.const_mul c).intervalIntegrable 0 1) (hcontc.intervalIntegrable 0 1)
  have hE1 : E 1 = 1 := by
    simp only [hE, Complex.ofReal_one, mul_one]
    rw [hc_def]
    have := exp_char_one k
    simpa [Complex.ofReal_one] using this
  have hE0 : E 0 = 1 := by simp [hE]
  have hG1 : ((meanZeroPrimitive ξ 1 : ℝ) : ℂ) = ((meanZeroPrimitive ξ 0 : ℝ) : ℂ) := by
    rw [meanZeroPrimitive_one hξ]
  -- `∫ E · (ξ - m) = ∫ E · ξ` since `∫ E = 0`.
  have hEzero : ∫ x in (0 : ℝ)..1, E x = 0 := integral_fourier_char_eq_zero hk
  have hsplit : ∫ x in (0 : ℝ)..1, E x * ((ξ (x : UnitAddCircle) - circleMean ξ : ℝ) : ℂ) =
      ∫ x in (0 : ℝ)..1, E x * ((ξ (x : UnitAddCircle) : ℝ) : ℂ) := by
    have hpt : ∀ x : ℝ, E x * ((ξ (x : UnitAddCircle) - circleMean ξ : ℝ) : ℂ) =
        E x * ((ξ (x : UnitAddCircle) : ℝ) : ℂ) - (circleMean ξ : ℂ) * E x := by
      intro x; push_cast; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub hEξ hcEm, intervalIntegral.integral_const_mul,
      hEzero, mul_zero, sub_zero]
  have hEG : ∫ x in (0 : ℝ)..1, c * E x * ((meanZeroPrimitive ξ x : ℝ) : ℂ) =
      c * ∫ x in (0 : ℝ)..1, E x * ((meanZeroPrimitive ξ x : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  rw [hE1, hE0, hG1, one_mul, sub_self, zero_sub, hEG] at hibp
  have hXi : circleCoeff (circlePrimitive hξ) k =
      ∫ x in (0 : ℝ)..1, E x * ((meanZeroPrimitive ξ x : ℝ) : ℂ) := by
    rw [circleCoeff_eq_intervalIntegral]
    simp only [circlePrimitive_coe]
    rfl
  have hxi : circleCoeff ξ k = ∫ x in (0 : ℝ)..1, E x * ((ξ (x : UnitAddCircle) : ℝ) : ℂ) := by
    rw [circleCoeff_eq_intervalIntegral]
  rw [hXi, hxi, ← hsplit, hibp, hc_def]
  push_cast
  ring

end Primitive

end Riesz1
