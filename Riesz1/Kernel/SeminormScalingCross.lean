/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.SeminormScalingCircle
public import Mathlib.Analysis.PSeries

/-!
# Cross terms between the periodization and the line

The difference between the unit-circle increment and the line increment of a function supported
in `[-ρ, ρ]` with `ρ < 1/2` is a finite sum of autocorrelations at integer shifts. The sums are
finite on the central cell, so no interchange of infinite sums and integrals is needed there.
-/

public section

open MeasureTheory Set
open scoped ComplexConjugate

namespace Riesz1

/-- The autocorrelation `v ↦ ∫ g(x + v) conj(g x) dx` of a function on the line. -/
@[expose]
noncomputable def autocorr (g : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∫ x, g (x + v) * conj (g x)

/-- The squared modulus of a difference of complex numbers. -/
private lemma norm_sub_sq_complex (a b : ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * conj b).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

/-- The product `g(x + c) conj(g x)` of two square-integrable translates is integrable. -/
theorem integrable_shift_mul_conj {g : ℝ → ℂ} (hg2 : MemLp g 2 volume) (c : ℝ) :
    Integrable (fun x => g (x + c) * conj (g x)) := by
  have h1 : MemLp (fun x => g (x + c)) 2 volume :=
    hg2.comp_measurePreserving (measurePreserving_add_right volume c)
  have h2 : MemLp (fun x => conj (g x)) 2 volume := hg2.star
  exact MemLp.integrable_mul h1 h2

/-- Outside the central cell a function supported in `[-ρ, ρ]` vanishes. -/
theorem eq_zero_of_not_mem_cell {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) {x : ℝ} (hx : x ∉ Ioc (-(1 / 2 : ℝ)) (1 / 2)) :
    g x = 0 := by
  apply hsupp
  rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

/-- The autocorrelation vanishes beyond twice the support radius. -/
theorem autocorr_eq_zero {g : ℝ → ℂ} {ρ : ℝ} (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) {v : ℝ}
    (hv : 2 * ρ < |v|) : autocorr g v = 0 := by
  unfold autocorr
  have h0 : ∀ x : ℝ, g (x + v) * conj (g x) = 0 := by
    intro x
    by_cases hx : ρ < |x|
    · simp [hsupp x hx]
    · by_cases hxv : ρ < |x + v|
      · simp [hsupp _ hxv]
      · exfalso
        simp only [not_lt] at hx hxv
        have h := abs_sub (x + v) x
        have e : x + v - x = v := by ring
        rw [e] at h
        linarith
  simp [h0]

/-- The cell integral of the product of a periodization with a conjugate periodization is a
finite sum of autocorrelations. -/
theorem integral_cell_periodize_mul_conj {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (hg2 : MemLp g 2 volume) (u : ℝ) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), unitPeriodize g (x + u) * conj (unitPeriodize g x) =
      ∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), autocorr g (u + m) := by
  have hcongr : EqOn (fun x => unitPeriodize g (x + u) * conj (unitPeriodize g x))
      (fun x => ∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), g (x + (u + m)) * conj (g x))
      (uIcc (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro x hx
    rw [uIcc_of_le (by norm_num), mem_Icc] at hx
    have hab : |x| ≤ 1 / 2 := abs_le.mpr ⟨hx.1, hx.2⟩
    simp only
    rw [unitPeriodize_add_eq_sum hρ hsupp u hab, unitPeriodize_eq_of_mem_cell hρ hsupp hab,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [add_assoc]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [intervalIntegral.integral_of_le (by norm_num),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    · intro x hx
      rw [eq_zero_of_not_mem_cell hρ hsupp hx, map_zero, mul_zero]
  · intro m _
    have hint := (integrable_shift_mul_conj hg2 (u + m)).intervalIntegrable
      (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    exact hint

/-- The periodization is square integrable on the central cell. -/
theorem memLp_unitPeriodize_cell {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (hg2 : MemLp g 2 volume) :
    MemLp (unitPeriodize g) 2 (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) := by
  refine MemLp.ae_eq ?_ (hg2.restrict _)
  refine ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
  rw [mem_Ioc] at hx
  exact (unitPeriodize_eq_of_mem_cell hρ hsupp (abs_le.mpr ⟨hx.1.le, hx.2⟩)).symm

/-- Translation invariance of the squared periodization over one period. -/
theorem integral_cell_norm_sq_periodize_add (g : ℝ → ℂ) (u : ℝ) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖unitPeriodize g (x + u)‖ ^ 2 =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖unitPeriodize g x‖ ^ 2 := by
  have hper : Function.Periodic (fun x => ‖unitPeriodize g x‖ ^ 2) 1 := fun x => by
    simp only [unitPeriodize_periodic g x]
  have h1 := intervalIntegral.integral_comp_add_right
    (fun x => ‖unitPeriodize g x‖ ^ 2) u (a := -(1 / 2 : ℝ)) (b := 1 / 2)
  have h2 := hper.intervalIntegral_add_eq (-(1 / 2 : ℝ) + u) (-(1 / 2 : ℝ))
  rw [show (-(1 / 2 : ℝ) + u + 1) = 1 / 2 + u by ring,
    show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num] at h2
  exact h1.trans h2

/-- On the central cell the squared periodization integrates to the line integral. -/
theorem integral_cell_norm_sq_periodize {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖unitPeriodize g x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [eq_zero_of_not_mem_cell hρ hsupp hx]
    simp
  · have hx' : |x| ≤ 1 / 2 := by
      rw [mem_Ioc] at hx
      exact abs_le.mpr ⟨hx.1.le, hx.2⟩
    rw [unitPeriodize_eq_of_mem_cell hρ hsupp hx']

/-- The line increment identity: the squared increment integrates to twice the squared norm
minus twice the autocorrelation. -/
theorem integral_norm_sub_sq_line {g : ℝ → ℂ} (hg2 : MemLp g 2 volume) (u : ℝ) :
    ∫ x, ‖g (x + u) - g x‖ ^ 2 = 2 * (∫ x, ‖g x‖ ^ 2) - 2 * (autocorr g u).re := by
  have hA : Integrable (fun x => ‖g (x + u)‖ ^ 2) := by
    have h1 : MemLp (fun x => g (x + u)) 2 volume :=
      hg2.comp_measurePreserving (measurePreserving_add_right volume u)
    exact h1.integrable_norm_pow (by norm_num) |>.congr (ae_of_all _ (fun x => by simp))
  have hB : Integrable (fun x => ‖g x‖ ^ 2) := by
    exact hg2.integrable_norm_pow (by norm_num)
  have hC : Integrable (fun x => (g (x + u) * conj (g x)).re) :=
    (integrable_shift_mul_conj hg2 u).re
  have hAB : Integrable (fun x => ‖g (x + u)‖ ^ 2 + ‖g x‖ ^ 2) := hA.add hB
  have hC2 : Integrable (fun x => 2 * (g (x + u) * conj (g x)).re) := hC.const_mul 2
  have hre : ∫ x, (g (x + u) * conj (g x)).re = (autocorr g u).re := by
    unfold autocorr
    exact integral_re (integrable_shift_mul_conj hg2 u)
  have hsh : ∫ x, ‖g (x + u)‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 :=
    integral_add_right_eq_self (fun x => ‖g x‖ ^ 2) u
  have hpt : ∀ x, ‖g (x + u) - g x‖ ^ 2 =
      ‖g (x + u)‖ ^ 2 + ‖g x‖ ^ 2 - 2 * (g (x + u) * conj (g x)).re :=
    fun x => norm_sub_sq_complex _ _
  have hsplit : ∫ x, (‖g (x + u)‖ ^ 2 + ‖g x‖ ^ 2 - 2 * (g (x + u) * conj (g x)).re) =
      (∫ x, ‖g (x + u)‖ ^ 2) + (∫ x, ‖g x‖ ^ 2) - 2 * (∫ x, (g (x + u) * conj (g x)).re) := by
    rw [integral_sub hAB hC2, integral_add hA hB, integral_const_mul]
  simp_rw [hpt]
  rw [hsplit, hre, hsh]
  ring

/-- On the central cell, the squared increment of the periodization integrates to twice the
squared norm minus twice the finite sum of autocorrelations. -/
theorem integral_cell_norm_sub_sq {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (hg2 : MemLp g 2 volume) (u : ℝ) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖unitPeriodize g (x + u) - unitPeriodize g x‖ ^ 2 =
      2 * (∫ x, ‖g x‖ ^ 2) -
        2 * (∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), autocorr g (u + m)).re := by
  have hGu := memLp_unitPeriodize_add_cell hρ hsupp hg2 u
  have hGc := memLp_unitPeriodize_cell hρ hsupp hg2
  have hGc' : MemLp (fun x => conj (unitPeriodize g x)) 2
      (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) := hGc.star
  have hA : IntervalIntegrable (fun x => ‖unitPeriodize g (x + u)‖ ^ 2) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hGu.integrable_norm_pow (by norm_num)
  have hB : IntervalIntegrable (fun x => ‖unitPeriodize g x‖ ^ 2) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hGc.integrable_norm_pow (by norm_num)
  have hprod : Integrable (fun x => unitPeriodize g (x + u) * conj (unitPeriodize g x))
      (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) := MemLp.integrable_mul hGu hGc'
  have hC : IntervalIntegrable (fun x => (unitPeriodize g (x + u) * conj (unitPeriodize g x)).re)
      volume (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hprod.re
  have hC_int : IntervalIntegrable (fun x => unitPeriodize g (x + u) * conj (unitPeriodize g x))
      volume (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hprod
  have hcross : ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
      (unitPeriodize g (x + u) * conj (unitPeriodize g x)).re =
        (∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), autocorr g (u + m)).re := by
    have hre := intervalIntegral.intervalIntegral_re hC_int
    simp only [RCLike.re_to_complex] at hre
    rw [hre, integral_cell_periodize_mul_conj hρ hsupp hg2 u]
  have hsh := integral_cell_norm_sq_periodize_add g u
  have hcell := integral_cell_norm_sq_periodize hρ hsupp
  have hpt : ∀ x, ‖unitPeriodize g (x + u) - unitPeriodize g x‖ ^ 2 =
      ‖unitPeriodize g (x + u)‖ ^ 2 + ‖unitPeriodize g x‖ ^ 2 -
        2 * (unitPeriodize g (x + u) * conj (unitPeriodize g x)).re :=
    fun x => norm_sub_sq_complex _ _
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub (hA.add hB) (hC.const_mul 2),
    intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul, hcross, hsh, hcell]
  ring

/-- The difference of the two increments is the negative real part of the finite sum of
autocorrelations at nonzero shifts, plus the zero-shift term. -/
theorem cell_line_difference {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (hg2 : MemLp g 2 volume) (u : ℝ) :
    (1 / 2 : ℝ) * (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        ‖unitPeriodize g (x + u) - unitPeriodize g x‖ ^ 2) -
      (1 / 2 : ℝ) * (∫ x, ‖g (x + u) - g x‖ ^ 2) =
        (autocorr g u).re -
          (∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), autocorr g (u + m)).re := by
  rw [integral_cell_norm_sub_sq hρ hsupp hg2 u, integral_norm_sub_sq_line hg2 u]
  ring

/-- A shift outside the central window is at distance more than `1 + |u|` from the origin. -/
private lemma one_add_abs_lt_abs_of_not_mem {u : ℝ} {m : ℤ}
    (hm : m ∉ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1)) : 1 + |u| < |(m : ℝ)| := by
  have hmabs : ⌈|u|⌉ + 1 < |m| := by
    by_contra h
    simp only [not_lt] at h
    exact hm (Finset.mem_Icc.mpr (abs_le.mp h))
  have hc : |u| ≤ (⌈|u|⌉ : ℝ) := Int.le_ceil |u|
  have hcast : ((⌈|u|⌉ + 1 : ℤ) : ℝ) < ((|m| : ℤ) : ℝ) := by exact_mod_cast hmabs
  rw [Int.cast_abs] at hcast
  push_cast at hcast
  linarith

/-- The finite sum of autocorrelations over the window, minus the zero shift, is the sum over
nonzero shifts. -/
theorem sum_autocorr_sub_eq_tsum {g : ℝ → ℂ} {ρ : ℝ} (hρ : ρ < 1 / 2)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (u : ℝ) :
    (∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), autocorr g (u + m)) - autocorr g u =
      ∑' m : ℤ, (if m = 0 then 0 else autocorr g (u + m)) := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1) := by
    rw [Finset.mem_Icc]
    have : 0 ≤ ⌈|u|⌉ := Int.ceil_nonneg (abs_nonneg u)
    constructor <;> linarith
  rw [tsum_eq_sum (s := Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1))]
  · have hsplit : ∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), autocorr g (u + m) =
        autocorr g u + ∑ m ∈ (Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1)).erase 0,
          autocorr g (u + m) := by
      rw [← Finset.add_sum_erase _ _ h0]
      simp
    have hsplit2 : ∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1),
        (if m = 0 then (0 : ℂ) else autocorr g (u + m)) =
        ∑ m ∈ (Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1)).erase 0, autocorr g (u + m) := by
      rw [← Finset.add_sum_erase _ _ h0]
      simp only [ite_true, zero_add]
      exact Finset.sum_congr rfl (fun m hm => by rw [ite_eq_right (Finset.ne_of_mem_erase hm)])
    rw [hsplit, hsplit2]
    ring
  · intro m hm
    have hne : m ≠ 0 := fun h => hm (h ▸ h0)
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne), autocorr_eq_zero hsupp]
    have hbig := one_add_abs_lt_abs_of_not_mem hm
    have hu : |u| ≥ 0 := abs_nonneg u
    have htri : |(m : ℝ)| ≤ |u + m| + |u| := by
      have h := abs_sub (u + m) u
      have e : u + m - u = (m : ℝ) := by ring
      rw [e] at h
      exact h
    have : 2 * ρ < |u + m| := by linarith
    exact this

/-- The autocorrelation is measurable for a measurable function on the line. -/
theorem measurable_autocorr {g : ℝ → ℂ} (hg : Measurable g) : Measurable (autocorr g) := by
  have hF : StronglyMeasurable (Function.uncurry fun (v x : ℝ) => g (x + v) * conj (g x)) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  exact (hF.integral_prod_right (ν := volume)).measurable

/-- The `L¹` norm of the autocorrelation is at most the square of the `L¹` norm. -/
theorem lintegral_enorm_autocorr_le {g : ℝ → ℂ} (hg : Measurable g) :
    ∫⁻ v, ‖autocorr g v‖ₑ ≤ (∫⁻ x, ‖g x‖ₑ) ^ 2 := by
  have hmeas : Measurable (fun p : ℝ × ℝ => ‖g (p.1 + p.2)‖ₑ * ‖g p.1‖ₑ) := by
    fun_prop
  calc ∫⁻ v, ‖autocorr g v‖ₑ ≤ ∫⁻ v, ∫⁻ x, ‖g (x + v)‖ₑ * ‖g x‖ₑ := by
        refine lintegral_mono (fun v => ?_)
        unfold autocorr
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        refine lintegral_congr (fun x => ?_)
        simp [enorm_mul]
    _ = ∫⁻ x, ∫⁻ v, ‖g (x + v)‖ₑ * ‖g x‖ₑ := by
        rw [lintegral_lintegral_swap]
        exact (hmeas.comp measurable_swap).aemeasurable
    _ = ∫⁻ x, (∫⁻ y, ‖g y‖ₑ) * ‖g x‖ₑ := by
        refine lintegral_congr (fun x => ?_)
        rw [lintegral_mul_const _ (by fun_prop)]
        congr 1
        exact lintegral_add_left_eq_self (fun y => ‖g y‖ₑ) x
    _ = (∫⁻ y, ‖g y‖ₑ) * ∫⁻ x, ‖g x‖ₑ := lintegral_const_mul _ (by fun_prop)
    _ = (∫⁻ x, ‖g x‖ₑ) ^ 2 := by rw [sq, mul_comm]

/-- The coefficient of the shifted weighted estimate, at shift `m`. -/
@[expose]
noncomputable def shiftCoeff (ρ τ : ℝ) (m : ℤ) : ℝ :=
  (((1 - 2 * ρ) * |(m : ℝ)|) ^ (1 + τ))⁻¹

/-- One shifted weighted estimate: the weight `|u|^{-(1+τ)}` at the argument `u + m` is at most
`shiftCoeff`, times the `L¹` norm of the autocorrelation. -/
theorem lintegral_weight_autocorr_shift_le {g : ℝ → ℂ} {ρ τ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < 1 / 2) (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (hτ : 0 < τ) {m : ℤ} (hm : m ≠ 0) :
    ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) * ‖autocorr g (u + m)‖ₑ ≤
      ENNReal.ofReal (shiftCoeff ρ τ m) * ∫⁻ v, ‖autocorr g v‖ₑ := by
  have hshift : ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) * ‖autocorr g (u + m)‖ₑ =
      ∫⁻ v : ℝ, ENNReal.ofReal ((|v - m| ^ (1 + τ))⁻¹) * ‖autocorr g v‖ₑ := by
    have h := lintegral_add_right_eq_self (μ := volume)
      (fun v : ℝ => ENNReal.ofReal ((|v - (m : ℝ)| ^ (1 + τ))⁻¹) * ‖autocorr g v‖ₑ) (m : ℝ)
    simp only [add_sub_cancel_right] at h
    exact h
  rw [hshift, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono (fun v => ?_)
  by_cases hv : 2 * ρ < |v|
  · rw [autocorr_eq_zero hsupp hv]
    simp
  · simp only [not_lt] at hv
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
      rwa [Int.cast_abs, Int.cast_one] at h2
    have htri : |(m : ℝ)| ≤ |v - m| + |v| := by
      have h := abs_sub (v - m) v
      have e : v - m - v = -(m : ℝ) := by ring
      rw [e, abs_neg] at h
      exact h
    have hlow : (1 - 2 * ρ) * |(m : ℝ)| ≤ |v - m| := by nlinarith
    have hpos : 0 < (1 - 2 * ρ) * |(m : ℝ)| := by
      have : 0 < 1 - 2 * ρ := by linarith
      nlinarith
    have hle : ((1 - 2 * ρ) * |(m : ℝ)|) ^ (1 + τ) ≤ |v - m| ^ (1 + τ) :=
      Real.rpow_le_rpow hpos.le hlow (by linarith)
    have hinv : (|v - m| ^ (1 + τ))⁻¹ ≤ shiftCoeff ρ τ m :=
      inv_anti₀ (Real.rpow_pos_of_pos hpos _) hle
    gcongr

/-- The shift coefficients are summable over the integers. -/
theorem summable_shiftCoeff {ρ τ : ℝ} (hρ : ρ < 1 / 2) (hτ : 0 < τ) :
    Summable (shiftCoeff ρ τ) := by
  have hb : 1 < 1 + τ := by linarith
  refine ((Real.summable_abs_int_rpow hb).mul_left (((1 - 2 * ρ) ^ (1 + τ))⁻¹)).congr (fun m => ?_)
  unfold shiftCoeff
  rw [Real.mul_rpow (by linarith) (abs_nonneg _), mul_inv, ← Real.rpow_neg (abs_nonneg _)]

/-- Summing the weighted shift estimate over the nonzero shifts. -/
theorem lintegral_weight_autocorr_tsum_le {g : ℝ → ℂ} {ρ τ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < 1 / 2) (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0) (hg : Measurable g) (hτ : 0 < τ) :
    ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
        (∑' m : ℤ, ‖if m = 0 then (0 : ℂ) else autocorr g (u + m)‖ₑ) ≤
      (∑' m : ℤ, ENNReal.ofReal (shiftCoeff ρ τ m)) * ∫⁻ v, ‖autocorr g v‖ₑ := by
  have hmA := measurable_autocorr hg
  have hmeasm : ∀ m : ℤ, Measurable (fun u : ℝ => ‖if m = 0 then (0 : ℂ) else
      autocorr g (u + m)‖ₑ) := by
    intro m
    by_cases hm : m = 0
    · simp only [hm, ite_true]
      exact measurable_const.enorm
    · simp only [hm, ite_false]
      exact (hmA.comp (measurable_id.add_const _)).enorm
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun (m : ℤ) (u : ℝ) => ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
      ‖if m = 0 then (0 : ℂ) else autocorr g (u + m)‖ₑ) (fun m => by
        have hw : Measurable (fun u : ℝ => ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹)) := by fun_prop
        exact (hw.mul (hmeasm m)).aemeasurable),
    ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum (fun m => ?_)
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ite_false]
    exact lintegral_weight_autocorr_shift_le hρ0 hρ hsupp hτ hm

/-- A shift outside the central window contributes nothing to the circle cross terms. -/
theorem autocorr_shift_eq_zero_of_not_mem {g : ℝ → ℂ} {ρ : ℝ} (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0)
    (hρ : ρ < 1 / 2) (u : ℝ) {m : ℤ} (hm : m ∉ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1)) :
    (if m = 0 then (0 : ℂ) else autocorr g (u + m)) = 0 := by
  have hne : m ≠ 0 := by
    intro h
    apply hm
    rw [h, Finset.mem_Icc]
    have : 0 ≤ ⌈|u|⌉ := Int.ceil_nonneg (abs_nonneg u)
    constructor <;> linarith
  rw [ite_eq_right hne]
  apply autocorr_eq_zero hsupp
  have hbig := one_add_abs_lt_abs_of_not_mem hm
  have hu : |u| ≥ 0 := abs_nonneg u
  have htri : |(m : ℝ)| ≤ |u + m| + |u| := by
    have h := abs_sub (u + m) u
    have e : u + m - u = (m : ℝ) := by ring
    rw [e] at h
    exact h
  linarith

/-- The autocorrelation sums over shifts are summable: only finitely many shifts contribute. -/
theorem summable_norm_autocorr_shift {g : ℝ → ℂ} {ρ : ℝ} (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0)
    (hρ : ρ < 1 / 2) (u : ℝ) :
    Summable (fun m : ℤ => ‖(if m = 0 then (0 : ℂ) else autocorr g (u + m))‖) := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1)) (fun m hm => ?_)
  rw [autocorr_shift_eq_zero_of_not_mem hsupp hρ u hm, norm_zero]

end Riesz1
