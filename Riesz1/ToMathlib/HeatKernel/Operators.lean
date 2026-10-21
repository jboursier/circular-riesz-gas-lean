/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.FractionalLaplacianCoeffs
public import Riesz1.Frozen.UnitLength
public import Riesz1.ToMathlib.HeatKernel.Circle
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Fractional Laplacians on the unit circle

For a smooth real function `f` on the unit circle `UnitAddCircle = ℝ / ℤ` and an exponent `s ∈ ℝ`,
the fractional Laplacian `(-Δ)^s f` is the Fourier series with multiplier
`fractionalLaplacianCoeffs` of the Riesz library: the coefficient at frequency `k` is
`|2πk|^{2s}` times the `k`-th Fourier coefficient of `f`. The exponent `s = γ` gives `(-Δ)^γ f`,
and `s = -γ` gives `(-Δ)^{-γ} f`.

This file proves that the Fourier coefficients of a smooth function decay faster than any
polynomial, hence that the Fourier series defining `(-Δ)^s f` converges absolutely and uniformly.
It also proves the Fourier expansion of the heat convolution `f ∗ W_t`, which the time-integral
formulas of Lemma 2.1 use in the files `OperatorsHeat` and `OperatorsSingular`.

See Lemma 2.1.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

open Complex (I)


/-- A function on the unit circle is smooth when its periodic lift `x ↦ f (x : UnitAddCircle)` is
`C^∞` on `ℝ`. -/
@[expose] def IsSmoothCircle (f : UnitAddCircle → ℝ) : Prop :=
  ContDiff ℝ ∞ fun x : ℝ => f (x : UnitAddCircle)

/-- The Fourier coefficient `∫_0^1 f(x) e^{-2πikx} dx` of a real function on the unit circle,
as a complex number. -/
@[expose] noncomputable def circleCoeff (f : UnitAddCircle → ℝ) (k : ℤ) : ℂ :=
  fourierCoeff (fun x : UnitAddCircle => (f x : ℂ)) k

/-- The fractional Laplacian `(-Δ)^s f` of a smooth function `f` on the unit circle, with exponent
`s ∈ ℝ`, as the Fourier series of `f` with multiplier `fractionalLaplacianCoeffs`. The exponent
`s = γ` gives `(-Δ)^γ f`, and `s = -γ` gives `(-Δ)^{-γ} f` on mean-zero functions. The series
converges absolutely and uniformly, so the sum is the value at every point. -/
@[expose] noncomputable def fracLapSeries (s : ℝ) (f : UnitAddCircle → ℝ) (_hf : IsSmoothCircle f)
    (x : ℝ) : ℂ :=
  ∑' k : ℤ, fractionalLaplacianCoeffs unitLength s (circleCoeff f) k * fourier k (x : UnitAddCircle)

/-- The circle convolution `(f ∗ W_t)(x) = ∫_0^1 f(x - y) W_t(y) dy` of a function on the unit
circle with the heat kernel at time `t > 0`. -/
@[expose] noncomputable def heatConvolution (f : UnitAddCircle → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, f ((x - y : ℝ) : UnitAddCircle) * circleHeatKernel t ht y

/-- The lift `u ↦ f (u : UnitAddCircle)` is periodic with period `1`. -/
lemma lift_periodic (f : UnitAddCircle → ℝ) :
    Function.Periodic (fun u : ℝ => f (u : UnitAddCircle)) 1 := by
  intro u
  simp only
  rw [AddCircle.coe_add_period]

/-- The multiplier `fractionalLaplacianCoeffs` on the unit circle is `|2πk|^{2s}` times the
coefficient, and vanishes at frequency zero. -/
lemma fractionalLaplacianCoeffs_unit (s : ℝ) (a : ℤ → ℂ) (k : ℤ) :
    fractionalLaplacianCoeffs unitLength s a k =
      if k = 0 then 0 else (|2 * π * (k : ℝ)| ^ (2 * s) : ℝ) * a k := by
  simp [fractionalLaplacianCoeffs, unitLength]

/-- The Fourier coefficient of a real function on the unit circle is the integral over `[0, 1]`
against the character `e^{-2πikx}`. -/
lemma circleCoeff_eq_intervalIntegral (f : UnitAddCircle → ℝ) (k : ℤ) :
    circleCoeff f k = ∫ x in (0 : ℝ)..1,
      Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * (f (x : UnitAddCircle) : ℂ) := by
  rw [circleCoeff, fourierCoeff_eq_intervalIntegral _ k 0]
  simp only [one_smul, zero_add, smul_eq_mul, fourier_coe_apply, div_one, Complex.ofReal_one]

/-- The zeroth Fourier coefficient is the integral of `f` over the circle. -/
lemma circleCoeff_zero (f : UnitAddCircle → ℝ) :
    circleCoeff f 0 = ((∫ x : UnitAddCircle, f x : ℝ) : ℂ) := by
  simp only [circleCoeff, fourierCoeff, neg_zero, fourier_zero, one_smul]
  rw [show (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm]
  rw [integral_complex_ofReal]

/-- The character `x ↦ e^{-2πikx}` has modulus one. -/
lemma norm_exp_two_pi_mul_I (k : ℤ) (x : ℝ) :
    ‖Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x)‖ = 1 := by
  rw [show 2 * π * I * ((-k : ℤ) : ℂ) * x = ((2 * π * ((-k : ℤ) : ℝ) * x : ℝ) : ℂ) * I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The Fourier character `fourier k` at a real point has modulus one. -/
lemma norm_fourier_coe (k : ℤ) (x : ℝ) : ‖fourier k (x : UnitAddCircle)‖ = 1 := by
  rw [fourier_coe_apply, Complex.ofReal_one, div_one,
    show 2 * π * I * (k : ℂ) * x = ((2 * π * (k : ℝ) * x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The modulus of `2πik` is `|2πk|`. -/
lemma norm_two_pi_mul_I_mul (k : ℤ) : ‖2 * π * I * (k : ℂ)‖ = |2 * π * (k : ℝ)| := by
  rw [show 2 * π * I * (k : ℂ) = ((2 * π * (k : ℝ) : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The derivative of a periodic function with period `1` is periodic with period `1`. -/
lemma periodic_deriv_of_periodic {G : ℝ → ℂ} (hper : Function.Periodic G 1) :
    Function.Periodic (deriv G) 1 := by
  intro x
  have h1 : (fun y : ℝ => G (y + 1)) = G := funext hper
  have h2 := deriv_comp_add_const (f := G) (a := (1 : ℝ)) (x := x)
  rw [h1] at h2
  exact h2.symm

/-- Integration by parts against a character on `[0, 1]`: the coefficient of a derivative is
`2πik` times the coefficient of the function, for a periodic `C^1` function. -/
lemma integral_deriv_mul_exp_eq (G : ℝ → ℂ) (hG : ContDiff ℝ 1 G)
    (hper : Function.Periodic G 1) (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * deriv G x =
      (2 * π * I * (k : ℂ)) * ∫ x in (0 : ℝ)..1,
        Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * G x := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℂ, E = fun x : ℝ => Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) :=
    ⟨_, rfl⟩
  have hEd : ∀ x : ℝ, HasDerivAt E (E x * (2 * π * I * ((-k : ℤ) : ℂ))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => (2 * π * I * ((-k : ℤ) : ℂ)) * (y : ℂ))
        (2 * π * I * ((-k : ℤ) : ℂ)) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (2 * π * I * ((-k : ℤ) : ℂ))
    rw [hE]
    exact h1.cexp
  have hGd : ∀ x : ℝ, HasDerivAt G (deriv G x) x := fun x =>
    ((hG.differentiable (by norm_num)) x).hasDerivAt
  have hGc : Continuous (deriv G) := hG.continuous_deriv (by norm_num)
  have hGcont : Continuous G := hG.continuous
  have hEc : Continuous E := by rw [hE]; fun_prop
  have hint1 : IntervalIntegrable (fun x => deriv G x * E x) volume 0 1 :=
    (hGc.mul hEc).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => G x * (E x * (2 * π * I * ((-k : ℤ) : ℂ))))
      volume 0 1 := (hGcont.mul (hEc.mul continuous_const)).intervalIntegrable _ _
  have hIBP := integral_deriv_mul_eq_sub_of_hasDerivAt (a := 0) (b := 1) (u := G) (v := E)
    (u' := deriv G) (v' := fun x => E x * (2 * π * I * ((-k : ℤ) : ℂ)))
    hGcont.continuousOn hEc.continuousOn
    (fun x _ => hGd x) (fun x _ => hEd x) (hGc.intervalIntegrable _ _)
    ((hEc.mul continuous_const).intervalIntegrable _ _)
  have hb0 : G 1 = G 0 := by simpa using hper 0
  have hE1 : E 1 = 1 := by
    rw [hE]
    simp only
    rw [show 2 * π * I * ((-k : ℤ) : ℂ) * ((1 : ℝ) : ℂ) = ((-k : ℤ) : ℂ) * (2 * π * I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hE0 : E 0 = 1 := by rw [hE]; simp
  simp only [hb0, hE1, hE0, mul_one, sub_self] at hIBP
  rw [intervalIntegral.integral_add hint1 hint2] at hIBP
  have hmul : ∫ x in (0 : ℝ)..1, G x * (E x * (2 * π * I * ((-k : ℤ) : ℂ))) =
      (2 * π * I * ((-k : ℤ) : ℂ)) * ∫ x in (0 : ℝ)..1, G x * E x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  have hg1 : ∫ x in (0 : ℝ)..1, Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * deriv G x =
      ∫ x in (0 : ℝ)..1, deriv G x * E x := by
    congr 1
    funext x
    simp only [hE]
    ring
  have hg2 : ∫ x in (0 : ℝ)..1, Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * G x =
      ∫ x in (0 : ℝ)..1, G x * E x := by
    congr 1
    funext x
    simp only [hE]
    ring
  rw [hg1, hg2]
  push_cast at hIBP hmul ⊢
  linear_combination hIBP - hmul

/-- Iterated derivatives of a periodic function with period `1` are periodic. -/
lemma periodic_iterate_deriv {G : ℝ → ℂ} (hper : Function.Periodic G 1) (j : ℕ) :
    Function.Periodic (deriv^[j] G) 1 := by
  induction j with
  | zero => simpa using hper
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact periodic_deriv_of_periodic ih

/-- The Fourier coefficient of the `j`-th derivative is `(2πik)^j` times the coefficient of the
function, for a periodic smooth function. -/
lemma integral_iterate_deriv_mul_exp (k : ℤ) (j : ℕ) (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (hper : Function.Periodic G 1) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * (deriv^[j] G) x =
      (2 * π * I * (k : ℂ)) ^ j * ∫ x in (0 : ℝ)..1,
        Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * G x := by
  induction j generalizing G with
  | zero => simp
  | succ j ih =>
    have hG' : ContDiff ℝ ∞ (deriv G) := (contDiff_infty_iff_deriv.mp hG).2
    have hG1 : ContDiff ℝ 1 G := hG.of_le (by simp)
    rw [Function.iterate_succ_apply, ih (deriv G) hG' (periodic_deriv_of_periodic hper),
      integral_deriv_mul_exp_eq G hG1 hper k, pow_succ]
    ring

/-- The Fourier coefficients of a smooth function are bounded after multiplication by any power
of `|2πk|`. -/
lemma exists_bound_circleCoeff (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) (j : ℕ) :
    ∃ C : ℝ, ∀ k : ℤ, ‖circleCoeff f k‖ * |2 * π * (k : ℝ)| ^ j ≤ C := by
  set G : ℝ → ℂ := fun x => ((f (x : UnitAddCircle) : ℝ) : ℂ) with hGdef
  have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hf
  have hper : Function.Periodic G 1 := fun x => by
    simp only [hGdef]
    rw [AddCircle.coe_add_period]
  have hGj : Continuous (deriv^[j] G) := (hG.iterate_deriv j).continuous
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hGj.continuousOn
  refine ⟨M, fun k => ?_⟩
  have hcoeff : circleCoeff f k = ∫ x in (0 : ℝ)..1,
      Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * G x :=
    circleCoeff_eq_intervalIntegral f k
  have hbound : ‖∫ x in (0 : ℝ)..1,
      Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * (deriv^[j] G) x‖ ≤ M := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := M)
      (f := fun x => Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * x) * (deriv^[j] G) x)
      (fun x hx => by
        rw [uIoc_of_le zero_le_one] at hx
        rw [norm_mul, norm_exp_two_pi_mul_I, one_mul]
        exact hM x (Ioc_subset_Icc_self hx))
    simpa using h
  rw [integral_iterate_deriv_mul_exp k j G hG hper, ← hcoeff, norm_mul, norm_pow,
    norm_two_pi_mul_I_mul] at hbound
  rw [mul_comm]
  exact hbound

/-- The Fourier coefficients of a smooth function are absolutely summable after weighting by a
power of `|2πk|`. -/
lemma summable_norm_two_pi_pow_mul (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) (p : ℕ) :
    Summable fun k : ℤ => |2 * π * (k : ℝ)| ^ p * ‖circleCoeff f k‖ := by
  obtain ⟨C, hC⟩ := exists_bound_circleCoeff f hf (p + 2)
  have hev : ∀ᶠ k : ℤ in cofinite, k ≠ 0 :=
    Filter.eventually_cofinite.2 ((Set.finite_singleton (0 : ℤ)).subset fun k hk => by
      simpa using hk)
  refine Summable.of_norm_bounded_eventually
    (((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)).mul_left (C / (2 * π) ^ 2)) ?_
  filter_upwards [hev] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  set a : ℝ := |2 * π * (k : ℝ)| with ha_def
  have ha_pos : 0 < a := abs_pos.2 (by positivity)
  have ha2 : a ^ 2 = (2 * π) ^ 2 * (k : ℝ) ^ 2 := by
    rw [ha_def, sq_abs]
    ring
  rw [Real.norm_of_nonneg (by positivity)]
  have hrhs : C / (2 * π) ^ 2 * (1 / (k : ℝ) ^ 2) = C / a ^ 2 := by
    rw [ha2]
    field_simp
  rw [hrhs, le_div_iff₀ (by positivity)]
  have hC' := hC k
  calc a ^ p * ‖circleCoeff f k‖ * a ^ 2 = ‖circleCoeff f k‖ * a ^ (p + 2) := by ring
    _ ≤ C := hC'

/-- The fractional Laplacian coefficients of a smooth function are absolutely summable. -/
lemma summable_norm_fracLapCoeff (s : ℝ) (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) :
    Summable fun k : ℤ => ‖fractionalLaplacianCoeffs unitLength s (circleCoeff f) k‖ := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (summable_norm_two_pi_pow_mul f hf (2 * ⌈|s|⌉₊))
  rw [fractionalLaplacianCoeffs_unit]
  by_cases hk : k = 0
  · subst hk
    simp only [ite_true, norm_zero]
    positivity
  · simp only [hk, ite_false, norm_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have h1 : (1 : ℝ) ≤ |2 * π * (k : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]
      nlinarith [Real.two_le_pi]
    have h2 : 2 * s ≤ ((2 * ⌈|s|⌉₊ : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil |s|, le_abs_self s]
    have h3 : |2 * π * (k : ℝ)| ^ (2 * s) ≤ |2 * π * (k : ℝ)| ^ (2 * ⌈|s|⌉₊) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by exact_mod_cast h2)
    exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

/-- The Fourier series defining `(-Δ)^s f` is absolutely convergent at every point. -/
lemma hasSum_fracLapSeries (s : ℝ) (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) (x : ℝ) :
    HasSum (fun k : ℤ => fractionalLaplacianCoeffs unitLength s (circleCoeff f) k *
      fourier k (x : UnitAddCircle)) (fracLapSeries s f hf x) := by
  have hsum : Summable (fun k : ℤ => fractionalLaplacianCoeffs unitLength s (circleCoeff f) k *
      fourier k (x : UnitAddCircle)) := by
    refine Summable.of_norm_bounded (summable_norm_fracLapCoeff s f hf) (fun k => ?_)
    rw [norm_mul, norm_fourier_coe, mul_one]
  exact hsum.hasSum

/-- The fractional Laplacian series converges uniformly in `x`, by the Weierstrass test with the
summable sequence `‖fractionalLaplacianCoeffs ... k‖`. -/
lemma tendstoUniformly_fracLapSeries (s : ℝ) (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) :
    TendstoUniformly (fun (F : Finset ℤ) (x : ℝ) => ∑ k ∈ F,
      fractionalLaplacianCoeffs unitLength s (circleCoeff f) k * fourier k (x : UnitAddCircle))
      (fun x : ℝ => fracLapSeries s f hf x) atTop := by
  have hbound : ∀ (k : ℤ) (x : ℝ), ‖fractionalLaplacianCoeffs unitLength s (circleCoeff f) k *
      fourier k (x : UnitAddCircle)‖ ≤
        ‖fractionalLaplacianCoeffs unitLength s (circleCoeff f) k‖ := by
    intro k x
    rw [norm_mul, norm_fourier_coe, mul_one]
  exact tendstoUniformly_tsum (summable_norm_fracLapCoeff s f hf) hbound

/-- The lift of a smooth function on the unit circle is bounded. -/
lemma exists_bound_lift (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) :
    ∃ M : ℝ, ∀ u : ℝ, |f (u : UnitAddCircle)| ≤ M := by
  have hcont : Continuous fun u : ℝ => f (u : UnitAddCircle) :=
    (show ContDiff ℝ ∞ (fun u : ℝ => f (u : UnitAddCircle)) from hf).continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨M, fun u => ?_⟩
  obtain ⟨y, hy, hyu⟩ := (lift_periodic f).exists_mem_Ico₀ one_pos u
  rw [hyu]
  have := hM y (Ico_subset_Icc_self hy)
  simpa [Real.norm_eq_abs] using this

/-- Shifting the variable of an integrand that is periodic with period `1` leaves the integral
over one period unchanged. -/
lemma intervalIntegral_sub_eq_of_periodic {P : ℝ → ℂ} (hP : Function.Periodic P 1) (x : ℝ) :
    ∫ y in (0 : ℝ)..1, P (x - y) = ∫ z in (0 : ℝ)..1, P z := by
  rw [intervalIntegral.integral_comp_sub_left P x, sub_zero]
  have h := hP.intervalIntegral_add_eq (x - 1) 0
  rw [sub_add_cancel, zero_add] at h
  exact h

/-- The `k`-th Fourier mode of `f(x - ·)` against `e^{2πik·}` over one period. -/
lemma integral_convolution_exp (f : UnitAddCircle → ℝ) (k : ℤ) (x : ℝ) :
    ∫ y in (0 : ℝ)..1, ((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ) *
        Complex.exp (2 * π * I * (k : ℂ) * y) =
      fourier k (x : UnitAddCircle) * circleCoeff f k := by
  have hP : Function.Periodic (fun z : ℝ => Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * z) *
      ((f (z : UnitAddCircle) : ℝ) : ℂ)) 1 := by
    intro z
    simp only
    rw [AddCircle.coe_add_period,
      show 2 * π * I * ((-k : ℤ) : ℂ) * ((z + 1 : ℝ) : ℂ) =
        2 * π * I * ((-k : ℤ) : ℂ) * z + ((-k : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hint : ∀ y : ℝ, ((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ) *
      Complex.exp (2 * π * I * (k : ℂ) * y) =
        Complex.exp (2 * π * I * (k : ℂ) * x) * (Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) *
          ((x - y : ℝ) : ℂ)) * ((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ)) := by
    intro y
    have e : Complex.exp (2 * π * I * (k : ℂ) * y) = Complex.exp (2 * π * I * (k : ℂ) * x) *
        Complex.exp (2 * π * I * ((-k : ℤ) : ℂ) * ((x - y : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  have hsub := intervalIntegral_sub_eq_of_periodic hP x
  simp only [hint]
  rw [intervalIntegral.integral_const_mul, hsub, circleCoeff_eq_intervalIntegral,
    fourier_coe_apply, Complex.ofReal_one, div_one]

/-- The complex exponential series of the heat kernel is summable for `t > 0`. -/
lemma summable_heat_terms_complex {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Summable fun k : ℤ => Complex.exp ((-4 * π ^ 2 * (k : ℝ) ^ 2 * t : ℝ) : ℂ) *
      Complex.exp ((2 * π * (k : ℝ) * y : ℝ) * I) := by
  refine Summable.of_norm_bounded (summable_exp_neg_mul_sq t ht) (fun k => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The complex form of the heat kernel is a convergent series with the same terms. -/
lemma hasSum_heatKernel_complex {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasSum (fun k : ℤ => Complex.exp ((-4 * π ^ 2 * (k : ℝ) ^ 2 * t : ℝ) : ℂ) *
      Complex.exp ((2 * π * (k : ℝ) * y : ℝ) * I)) (circleHeatKernel t ht y : ℂ) := by
  rw [← circleHeatKernel_eq_complex_tsum t ht y]
  exact (summable_heat_terms_complex ht y).hasSum

/-- Fourier expansion of the heat convolution: for `t > 0`, the function `f ∗ W_t` has Fourier
series `∑_k e^{-4π²k²t} f̂(k) e_k`, with `e_k(x) = e^{2πikx}`. -/
theorem hasSum_heatConvolution (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    HasSum (fun k : ℤ => ((Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) : ℝ) : ℂ) *
      (fourier k (x : UnitAddCircle) * circleCoeff f k)) ((heatConvolution f ht x : ℝ) : ℂ) := by
  obtain ⟨M, hM⟩ := exists_bound_lift f hf
  have hfr : Continuous fun y : ℝ => f ((x - y : ℝ) : UnitAddCircle) :=
    (show ContDiff ℝ ∞ (fun u : ℝ => f (u : UnitAddCircle)) from hf).continuous.comp
      (continuous_const.sub continuous_id)
  have hfc : Continuous fun y : ℝ => ((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hfr
  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := 1)
    (F := fun (k : ℤ) (y : ℝ) => ((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ) *
      (Complex.exp ((-4 * π ^ 2 * (k : ℝ) ^ 2 * t : ℝ) : ℂ) *
        Complex.exp ((2 * π * (k : ℝ) * y : ℝ) * I)))
    (f := fun y : ℝ => ((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ) *
      (circleHeatKernel t ht y : ℂ))
    (bound := fun (k : ℤ) (_ : ℝ) => M * Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t))
    (fun k => (Continuous.mul hfc (by fun_prop)).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall fun y _ => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact mul_le_mul_of_nonneg_right (hM _) (Real.exp_pos _).le)
    (Filter.Eventually.of_forall fun _ _ => (summable_exp_neg_mul_sq t ht).mul_left M)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun y _ => (hasSum_heatKernel_complex ht y).mul_left _)
  beta_reduce at hDC
  have hval : ∫ y in (0 : ℝ)..1, ((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ) *
      (circleHeatKernel t ht y : ℂ) = ((heatConvolution f ht x : ℝ) : ℂ) := by
    rw [heatConvolution, ← intervalIntegral.integral_ofReal]
    congr 1
    funext y
    rw [Complex.ofReal_mul]
  have hterm : ∀ k : ℤ, ∫ y in (0 : ℝ)..1, ((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ) *
      (Complex.exp ((-4 * π ^ 2 * (k : ℝ) ^ 2 * t : ℝ) : ℂ) *
        Complex.exp ((2 * π * (k : ℝ) * y : ℝ) * I)) =
      ((Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) : ℝ) : ℂ) *
        (fourier k (x : UnitAddCircle) * circleCoeff f k) := by
    intro k
    have e : ∀ y : ℝ, ((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ) *
        (Complex.exp ((-4 * π ^ 2 * (k : ℝ) ^ 2 * t : ℝ) : ℂ) *
          Complex.exp ((2 * π * (k : ℝ) * y : ℝ) * I)) =
        Complex.exp ((-4 * π ^ 2 * (k : ℝ) ^ 2 * t : ℝ) : ℂ) *
          (((f ((x - y : ℝ) : UnitAddCircle) : ℝ) : ℂ) *
            Complex.exp (2 * π * I * (k : ℂ) * y)) := by
      intro y
      rw [show Complex.exp ((2 * π * (k : ℝ) * y : ℝ) * I) =
          Complex.exp (2 * π * I * (k : ℂ) * y) by congr 1; push_cast; ring]
      ring
    simp only [e]
    rw [intervalIntegral.integral_const_mul, integral_convolution_exp f k x,
      ← Complex.ofReal_exp]
  rw [hval] at hDC
  simp only [hterm] at hDC
  exact hDC

end Riesz1

end
