/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.SeminormScalingFourier
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Periodization on the unit circle

For a function `g` on the line supported in `[-ρ, ρ]` with `ρ < 1/2`, its one-periodization
`∑_m g(x + m)` agrees with `g` on the central cell `[-1/2, 1/2]`. The unit-circle Fourier
coefficients of the periodization are the line Fourier transform at the integers, and the
coefficients of its translate are those coefficients multiplied by `e^{2πiku} - 1`. These facts
turn the circle Sobolev seminorm into a sum over the integers.
-/

public section

open MeasureTheory Set FourierTransform

/-- The real inner product on the line is the product. -/
private lemma inner_real_mul (a b : ℝ) : inner ℝ a b = a * b := by
  simp [mul_comm]
open scoped ComplexConjugate

namespace Riesz1

/-- The one-periodization `x ↦ ∑_{m ∈ ℤ} g(x + m)` of a function on the line. -/
@[expose]
noncomputable def unitPeriodize (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' m : ℤ, g (x + m)

/-- The one-periodization is one-periodic. -/
theorem unitPeriodize_periodic (g : ℝ → ℂ) : Function.Periodic (unitPeriodize g) 1 := by
  intro x
  unfold unitPeriodize
  have h : ∀ m : ℤ, g (x + 1 + m) = g (x + ((m + 1 : ℤ) : ℝ)) := by
    intro m
    push_cast
    ring_nf
  simp only [h]
  exact Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun m : ℤ => g (x + m))

/-- On the central cell, the periodization of a function supported in `[-ρ, ρ]` is the function
itself. -/
theorem unitPeriodize_eq_of_mem_cell {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    unitPeriodize g x = g x := by
  unfold unitPeriodize
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro m hm
    apply hsupp
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
      rwa [Int.cast_abs, Int.cast_one] at h2
    have t1 : |(m : ℝ)| ≤ |x + m| + |x| := by
      have h := abs_sub (x + m) x
      have e : x + m - x = (m : ℝ) := by ring
      rw [e] at h
      exact h
    linarith

/-- For `|x| ≤ 1/2` the periodization of a translate is a finite sum over the integers in a
fixed finite range. The range depends only on the translation `u`. -/
theorem unitPeriodize_add_eq_sum {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (u : ℝ) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    unitPeriodize g (x + u) =
      ∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), g (x + u + m) := by
  unfold unitPeriodize
  apply tsum_eq_sum
  intro m hm
  apply hsupp
  have hmabs : ⌈|u|⌉ + 1 < |m| := by
    by_contra h
    simp only [not_lt] at h
    exact hm (Finset.mem_Icc.mpr (abs_le.mp h))
  have hreal : |u| + 1 < |(m : ℝ)| := by
    have hc : |u| ≤ (⌈|u|⌉ : ℝ) := Int.le_ceil |u|
    have hcast : ((⌈|u|⌉ + 1 : ℤ) : ℝ) < ((|m| : ℤ) : ℝ) := by exact_mod_cast hmabs
    rw [Int.cast_abs] at hcast
    push_cast at hcast
    linarith
  have t1 : |(m : ℝ)| ≤ |x + u + m| + |x + u| := by
    have h := abs_sub (x + u + m) (x + u)
    have e : x + u + m - (x + u) = (m : ℝ) := by ring
    rw [e] at h
    exact h
  have t2 : |x + u| ≤ |x| + |u| := abs_add_le x u
  linarith

/-- The unit-circle Fourier coefficients of the periodization are the line Fourier transform at
the integers. -/
theorem fourierCoeffOn_unitPeriodize {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (k : ℤ) :
    fourierCoeffOn (show (-(1 / 2 : ℝ)) < 1 / 2 by norm_num) (unitPeriodize g) k =
      𝓕 g (k : ℝ) := by
  rw [fourierCoeffOn_eq_integral _ _ (by norm_num)]
  have hcell : EqOn (fun x : ℝ => (fourier (-k) : AddCircle (1 / 2 - -(1 / 2) : ℝ) → ℂ)
      (x : AddCircle (1 / 2 - -(1 / 2) : ℝ)) • unitPeriodize g x)
      (fun x : ℝ => (fourier (-k) : AddCircle (1 / 2 - -(1 / 2) : ℝ) → ℂ)
      (x : AddCircle (1 / 2 - -(1 / 2) : ℝ)) • g x) (uIcc (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro x hx
    rw [uIcc_of_le (by norm_num), mem_Icc] at hx
    simp only
    rw [unitPeriodize_eq_of_mem_cell hρ hsupp (abs_le.mpr ⟨hx.1, hx.2⟩)]
  rw [intervalIntegral.integral_congr hcell]
  rw [intervalIntegral.integral_of_le (by norm_num),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [Real.fourier_eq]
    have hfour : ∀ x : ℝ, (fourier (-k) : AddCircle (1 / 2 - -(1 / 2) : ℝ) → ℂ)
        (x : AddCircle (1 / 2 - -(1 / 2) : ℝ)) = ((Real.fourierChar (-(x * k)) : Circle) : ℂ) := by
      intro x
      rw [fourier_coe_apply, Real.fourierChar_apply]
      norm_num
      congr 1
      ring
    simp only [hfour, inner_real_mul, Circle.smul_def, smul_eq_mul]
    norm_num
  · intro x hx
    have hbig : ρ < |x| := by
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    simp only [hsupp x hbig, smul_zero]

/-- On the cell, the unit-circle character `e^{-2πikx}` is the explicit exponential. -/
theorem fourier_neg_eq_fourierChar (k : ℤ) (y : ℝ) :
    (fourier (-k) : AddCircle (1 / 2 - -(1 / 2) : ℝ) → ℂ) (y : AddCircle (1 / 2 - -(1 / 2) : ℝ)) =
      ((Real.fourierChar (-(y * k)) : Circle) : ℂ) := by
  rw [fourier_coe_apply, Real.fourierChar_apply]
  norm_num
  congr 1
  ring

/-- The character `e^{-2πiky}` is one-periodic in `y`. -/
theorem fourierChar_neg_mul_add_one (y : ℝ) (k : ℤ) :
    ((Real.fourierChar (-((y + 1) * k)) : Circle) : ℂ) =
      ((Real.fourierChar (-(y * k)) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply]
  have h : ((2 * Real.pi * (-((y + 1) * k)) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * (-(y * k)) : ℝ) : ℂ) * Complex.I +
        ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Shifting the argument by `u` multiplies the character by `e^{2πiku}`. -/
theorem fourierChar_shift (y u : ℝ) (k : ℤ) :
    ((Real.fourierChar (-((y - u) * k)) : Circle) : ℂ) =
      ((Real.fourierChar (k * u)) : Circle) * ((Real.fourierChar (-(y * k)) : Circle) : ℂ) := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- Translating a one-periodic function multiplies its interval Fourier coefficient by
`e^{2πiku}`. -/
theorem fourierCoeffOn_comp_add_periodic {G : ℝ → ℂ} (hG : Function.Periodic G 1) (u : ℝ)
    (k : ℤ) :
    fourierCoeffOn (show (-(1 / 2 : ℝ)) < 1 / 2 by norm_num) (fun x => G (x + u)) k =
      ((Real.fourierChar (k * u) : Circle) : ℂ) *
        fourierCoeffOn (show (-(1 / 2 : ℝ)) < 1 / 2 by norm_num) G k := by
  rw [fourierCoeffOn_eq_integral _ _ (by norm_num), fourierCoeffOn_eq_integral _ _ (by norm_num)]
  simp only [fourier_neg_eq_fourierChar]
  norm_num
  set F : ℝ → ℂ := fun y => ((Real.fourierChar (-(y * k)) : Circle) : ℂ) * G y with hF
  have hFper : Function.Periodic F 1 := by
    intro y
    simp only [hF]
    rw [fourierChar_neg_mul_add_one, hG y]
  have hH : ∀ y : ℝ, ((Real.fourierChar (-((y - u) * k)) : Circle) : ℂ) * G y =
      ((Real.fourierChar (k * u)) : Circle) * F y := by
    intro y
    simp only [hF]
    rw [fourierChar_shift]
    ring
  have hsh : ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
      ((Real.fourierChar (-(x * k)) : Circle) : ℂ) * G (x + u) =
      ((Real.fourierChar (k * u)) : Circle) * ∫ x in (-(1 / 2 : ℝ))..(1 / 2), F x := by
    have h1 : ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        ((Real.fourierChar (-(x * k)) : Circle) : ℂ) * G (x + u) =
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
          ((Real.fourierChar (-(((x + u) - u) * k)) : Circle) : ℂ) * G (x + u) := by
      congr 1
      ext x
      rw [add_sub_cancel_right]
    rw [h1, intervalIntegral.integral_comp_add_right
      (fun y => ((Real.fourierChar (-((y - u) * k)) : Circle) : ℂ) * G y) u]
    simp only [hH]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have key := Function.Periodic.intervalIntegral_add_eq hFper (-(1 / 2 : ℝ) + u) (-(1 / 2 : ℝ))
    rw [show (-(1 / 2 : ℝ) + u + 1) = 1 / 2 + u by ring,
      show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num] at key
    exact key
  rw [hsh]

/-- A translate of the periodization is square integrable on the central cell. -/
theorem memLp_unitPeriodize_add_cell {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (hg2 : MemLp g 2 volume) (u : ℝ) :
    MemLp (fun x => unitPeriodize g (x + u)) 2 (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) := by
  have hS : (fun x => unitPeriodize g (x + u)) =ᵐ[volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))]
      (fun x => ∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), g (x + u + m)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
    rw [mem_Ioc] at hx
    exact unitPeriodize_add_eq_sum hρ hsupp u (abs_le.mpr ⟨hx.1.le, hx.2⟩)
  refine MemLp.ae_eq hS.symm ?_
  refine memLp_finsetSum _ (fun m _ => ?_)
  have h := (hg2.comp_measurePreserving (measurePreserving_add_right volume (u + m))).restrict
    (Ioc (-(1 / 2 : ℝ)) (1 / 2))
  convert h using 1
  funext x
  simp only [Function.comp_apply, add_assoc]

/-- Linearity of the interval Fourier coefficient for functions that are square integrable on
the central cell. -/
theorem fourierCoeffOn_sub_of_memLp {A B : ℝ → ℂ}
    (hA : MemLp A 2 (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))))
    (hB : MemLp B 2 (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2)))) (k : ℤ) :
    fourierCoeffOn (show (-(1 / 2 : ℝ)) < 1 / 2 by norm_num) (fun x => A x - B x) k =
      fourierCoeffOn (show (-(1 / 2 : ℝ)) < 1 / 2 by norm_num) A k -
        fourierCoeffOn (show (-(1 / 2 : ℝ)) < 1 / 2 by norm_num) B k := by
  have hint : ∀ C : ℝ → ℂ, MemLp C 2 (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) →
      IntervalIntegrable (fun x => ((Real.fourierChar (-(x * k)) : Circle) : ℂ) * C x) volume
        (-(1 / 2 : ℝ)) (1 / 2) := by
    intro C hC
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    refine Integrable.bdd_mul (c := 1) (hC.integrable one_le_two) ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ => ((Real.fourierChar (-(x * k)) : Circle) : ℂ)).aestronglyMeasurable
    · exact ae_of_all _ (fun x => by simp)
  rw [fourierCoeffOn_eq_integral _ _ (by norm_num), fourierCoeffOn_eq_integral _ _ (by norm_num),
    fourierCoeffOn_eq_integral _ _ (by norm_num)]
  simp only [fourier_neg_eq_fourierChar, smul_eq_mul, mul_sub]
  rw [intervalIntegral.integral_sub (hint A hA) (hint B hB), smul_sub]

/-- **Parseval for the periodized increment.** The weighted circle coefficients of a
periodized square-integrable function sum to half the squared increment of the periodization
over the central cell. -/
theorem hasSum_one_sub_cos_unitPeriodize {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (hg2 : MemLp g 2 volume) (u : ℝ) :
    HasSum (fun k : ℤ => (1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) * ‖𝓕 g (k : ℝ)‖ ^ 2)
      ((1 / 2 : ℝ) * ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        ‖unitPeriodize g (x + u) - unitPeriodize g x‖ ^ 2) := by
  have hab : (-(1 / 2 : ℝ)) < 1 / 2 := by norm_num
  have hGL : MemLp (unitPeriodize g) 2 (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) := by
    refine MemLp.ae_eq ?_ (hg2.restrict _)
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
    rw [mem_Ioc] at hx
    exact (unitPeriodize_eq_of_mem_cell hρ hsupp (abs_le.mpr ⟨hx.1.le, hx.2⟩)).symm
  have hf : MemLp (fun x => unitPeriodize g (x + u) - unitPeriodize g x) 2
      (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) :=
    (memLp_unitPeriodize_add_cell hρ hsupp hg2 u).sub hGL
  have hP := hasSum_sq_fourierCoeffOn hab hf
  have hcoef : ∀ k : ℤ, fourierCoeffOn hab (fun x => unitPeriodize g (x + u) - unitPeriodize g x) k
      = (((Real.fourierChar (k * u) : Circle) : ℂ) - 1) * 𝓕 g (k : ℝ) := by
    intro k
    rw [fourierCoeffOn_sub_of_memLp (memLp_unitPeriodize_add_cell hρ hsupp hg2 u) hGL k,
      fourierCoeffOn_comp_add_periodic (unitPeriodize_periodic g) u k,
      fourierCoeffOn_unitPeriodize hρ hsupp k]
    ring
  have hnorm : ∀ k : ℤ, ‖fourierCoeffOn hab (fun x => unitPeriodize g (x + u) - unitPeriodize g x) k‖ ^ 2
      = (2 - 2 * Real.cos (2 * Real.pi * ((k : ℝ) * u))) * ‖𝓕 g (k : ℝ)‖ ^ 2 := by
    intro k
    rw [hcoef k, norm_mul, mul_pow, norm_sq_fourierChar_sub_one]
  have hsum := hP.mul_left (1 / 2 : ℝ)
  simp only [hnorm] at hsum
  have h1 : ((1 / 2 : ℝ) - -(1 / 2)) ⁻¹ = 1 := by norm_num
  rw [h1, one_smul] at hsum
  have hfun : (fun k : ℤ => (1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) * ‖𝓕 g (k : ℝ)‖ ^ 2) =
      fun k : ℤ => (1 / 2 : ℝ) * ((2 - 2 * Real.cos (2 * Real.pi * ((k : ℝ) * u))) *
        ‖𝓕 g (k : ℝ)‖ ^ 2) := by
    funext k
    ring
  rw [hfun]
  exact hsum

end Riesz1
