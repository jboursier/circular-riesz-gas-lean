/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.SeminormScalingCore

/-!
# The converse core seminorm comparison

`seminorm_core_bound` in `SeminormScalingCore` assumes that the line seminorm is finite and
derives that the circle seminorm is finite. Here the roles are reversed: the circle seminorm is
finite, and the same pointwise cross-term domination gives the finiteness of the line seminorm,
with the same bound.
-/

public section

open MeasureTheory Set FourierTransform
open scoped ENNReal ComplexConjugate

namespace Riesz1

/-- Transfer of a bound through a positive constant: if `|b - a| ≤ B` then
`|κ a - κ b| ≤ κ B` for `κ ≥ 0`. -/
theorem abs_const_mul_sub_const_mul_le {κ a b B : ℝ} (hκ : 0 ≤ κ) (h : |b - a| ≤ B) :
    |κ * a - κ * b| ≤ κ * B := by
  calc |κ * a - κ * b| = κ * |a - b| := by rw [← mul_sub, abs_mul, abs_of_nonneg hκ]
    _ ≤ κ * B := mul_le_mul_of_nonneg_left (by rwa [abs_sub_comm]) hκ

/-- **Converse core seminorm comparison.** For a function supported in `[-ρ, ρ]` with `ρ < 1/2`
and finite circle seminorm, the line seminorm is finite and the two seminorms differ by at most
a constant times the squared `L¹` norm. -/
theorem seminorm_core_converse {τ ρ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2)
    {g : ℝ → ℂ} (hmeas : Measurable g) (hg1 : Integrable g) (hg2 : MemLp g 2 volume)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0)
    (hcirc : ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ τ * ‖𝓕 g (k : ℝ)‖ ^ 2) ≠ ⊤) :
    ∫⁻ η, ENNReal.ofReal (|η| ^ τ * ‖𝓕 g η‖ ^ 2) ≠ ⊤ ∧
      |(∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ τ * ‖𝓕 g (k : ℝ)‖ ^ 2)).toReal -
          (∫⁻ η, ENNReal.ofReal (|η| ^ τ * ‖𝓕 g η‖ ^ 2)).toReal| ≤
        (levyIntegral τ)⁻¹ * (∑' m : ℤ, shiftCoeff ρ τ m) * (∫ x, ‖g x‖) ^ 2 := by
  have hcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg1
  have hκpos : 0 < (levyIntegral τ)⁻¹ := inv_pos.mpr (levyIntegral_pos hτ hτ1)
  have hA := circle_seminorm_eq_lintegral hτ hτ1 g
  have hB := line_seminorm_eq_lintegral hτ hτ1 hcont
  -- Real-valued pieces of the cross-term decomposition, as in `seminorm_core_bound`.
  set P : ℝ → ℝ := fun u => (1 / 2 : ℝ) *
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖unitPeriodize g (x + u) - unitPeriodize g x‖ ^ 2 with hPdef
  set Q : ℝ → ℝ := fun u => (1 / 2 : ℝ) * ∫ x, ‖g (x + u) - g x‖ ^ 2 with hQdef
  set Mr : ℝ → ℝ := fun u => ∑' m : ℤ, ‖(if m = 0 then (0 : ℂ) else autocorr g (u + m))‖
    with hMdef
  have hsumP : ∀ u, HasSum (fun k : ℤ => (1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) *
      ‖𝓕 g (k : ℝ)‖ ^ 2) (P u) := fun u =>
    hasSum_one_sub_cos_unitPeriodize hρ hsupp hg2 u
  have hPnn : ∀ u, 0 ≤ P u := fun u => by
    simp only [hPdef]
    exact mul_nonneg (by norm_num)
      (intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity))
  have hQnn : ∀ u, 0 ≤ Q u := fun u => by
    simp only [hQdef]
    exact mul_nonneg (by norm_num) (integral_nonneg (fun x => by positivity))
  have hMnn : ∀ u, 0 ≤ Mr u := fun u =>
    tsum_nonneg (fun m => norm_nonneg _)
  -- The extended-valued circle sum equals `ofReal (P u)`.
  have hPe : ∀ u, (∑' k : ℤ, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) *
      ‖𝓕 g (k : ℝ)‖ ^ 2)) = ENNReal.ofReal (P u) := by
    intro u
    have hnn : ∀ k : ℤ, 0 ≤ (1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) *
        ‖𝓕 g (k : ℝ)‖ ^ 2 := fun k =>
      mul_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * ((k : ℝ) * u))]) (by positivity)
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hsumP u).summable, (hsumP u).tsum_eq]
  -- The extended-valued line integral equals `ofReal (Q u)`.
  have hQe : ∀ u, (∫⁻ η, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * (η * u))) *
      ‖𝓕 g η‖ ^ 2)) = ENNReal.ofReal (Q u) := by
    intro u
    have hint : Integrable (fun η : ℝ => (1 - Real.cos (2 * Real.pi * (η * u))) *
        ‖𝓕 g η‖ ^ 2) := by
      refine Integrable.bdd_mul (c := 2) (integrable_norm_sq_fourier hg1 hg2)
        (by fun_prop) (ae_of_all _ (fun η => ?_))
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [Real.cos_le_one (2 * Real.pi * (η * u)),
        Real.neg_one_le_cos (2 * Real.pi * (η * u))]
    have hnn : 0 ≤ᵐ[volume] (fun η : ℝ => (1 - Real.cos (2 * Real.pi * (η * u))) *
        ‖𝓕 g η‖ ^ 2) := ae_of_all _ (fun η => mul_nonneg
          (by linarith [Real.cos_le_one (2 * Real.pi * (η * u))]) (by positivity))
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    simp only [hQdef]
    rw [integral_one_sub_cos_norm_sq_fourier hg1 hg2 u]
  -- The extended-valued shift sum equals `ofReal (Mr u)`.
  have hMe : ∀ u, (∑' m : ℤ, ‖(if m = 0 then (0 : ℂ) else autocorr g (u + m))‖ₑ) =
      ENNReal.ofReal (Mr u) := by
    intro u
    simp only [hMdef]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _)
      (summable_norm_autocorr_shift hsupp hρ u)]
    congr 1
    funext m
    rw [ofReal_norm]
  -- The pointwise cross-term identity: the difference of the real quantities is bounded by Mr.
  have hdiff : ∀ u, |P u - Q u| ≤ Mr u := by
    intro u
    have h1 := cell_line_difference hρ hsupp hg2 u
    have h2 := sum_autocorr_sub_eq_tsum hρ hsupp u
    have hPQ : P u - Q u = -(∑' m : ℤ, (if m = 0 then (0 : ℂ) else autocorr g (u + m))).re := by
      simp only [hPdef, hQdef]
      rw [h1]
      have hsplit : (∑ m ∈ Finset.Icc (-(⌈|u|⌉ + 1)) (⌈|u|⌉ + 1), autocorr g (u + m)) =
          (∑' m : ℤ, (if m = 0 then (0 : ℂ) else autocorr g (u + m))) + autocorr g u := by
        rw [← h2]
        ring
      rw [hsplit, Complex.add_re]
      ring
    rw [hPQ, abs_neg]
    calc |(∑' m : ℤ, (if m = 0 then (0 : ℂ) else autocorr g (u + m))).re|
        ≤ ‖∑' m : ℤ, (if m = 0 then (0 : ℂ) else autocorr g (u + m))‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' m : ℤ, ‖(if m = 0 then (0 : ℂ) else autocorr g (u + m))‖ :=
          norm_tsum_le_tsum_norm (summable_norm_autocorr_shift hsupp hρ u)
  -- Measurability of the extended-valued pieces.
  have hw : Measurable (fun u : ℝ => ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹)) := by fun_prop
  have hPm : Measurable (fun u : ℝ => ∑' k : ℤ, ENNReal.ofReal ((1 - Real.cos
      (2 * Real.pi * ((k : ℝ) * u))) * ‖𝓕 g (k : ℝ)‖ ^ 2)) := by
    refine Measurable.tsum (fun k => ?_)
    fun_prop
  have hQm : Measurable (fun u : ℝ => ∫⁻ η, ENNReal.ofReal ((1 - Real.cos
      (2 * Real.pi * (η * u))) * ‖𝓕 g η‖ ^ 2)) := by
    have hjoint : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((1 - Real.cos
        (2 * Real.pi * (p.2 * p.1))) * ‖𝓕 g p.2‖ ^ 2)) := by fun_prop
    exact hjoint.lintegral_prod_right'
  have hMm : Measurable (fun u : ℝ => ∑' m : ℤ,
      ‖(if m = 0 then (0 : ℂ) else autocorr g (u + m))‖ₑ) := by
    refine Measurable.tsum (fun m => ?_)
    by_cases hm : m = 0
    · simp only [hm, ite_true]
      exact measurable_const.enorm
    · simp only [hm, ite_false]
      exact ((measurable_autocorr hmeas).comp (measurable_id.add_const _)).enorm
  -- Finiteness of the weighted shift sum, which does not involve the line seminorm.
  have hLg : ∫⁻ x, ‖g x‖ₑ ≠ ⊤ := hg1.hasFiniteIntegral.ne
  have hIac : ∫⁻ v, ‖autocorr g v‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.pow_ne_top hLg) (lintegral_enorm_autocorr_le hmeas)
  have hC1 : (∑' m : ℤ, ENNReal.ofReal (shiftCoeff ρ τ m)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (shiftCoeff_nonneg hρ) (summable_shiftCoeff hρ hτ)]
    exact ENNReal.ofReal_ne_top
  have hMfin : ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
      (∑' m : ℤ, ‖(if m = 0 then (0 : ℂ) else autocorr g (u + m))‖ₑ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hC1 hIac)
      (lintegral_weight_autocorr_tsum_le hρ0 hρ hsupp hmeas hτ)
  -- The circle side: finiteness of `hcirc` transfers to the weighted circle integral.
  have hPfin : ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
      (∑' k : ℤ, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) *
        ‖𝓕 g (k : ℝ)‖ ^ 2)) ≠ ⊤ := by
    intro htop
    apply hcirc
    rw [hA, htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hκpos).ne']
  -- Pointwise domination in the extended values, in both directions.
  have hPQe : ∀ u, ENNReal.ofReal (P u) ≤ ENNReal.ofReal (Q u) + ENNReal.ofReal (Mr u) := by
    intro u
    rw [← ENNReal.ofReal_add (hQnn u) (hMnn u)]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (hdiff u)).2])
  have hQPe : ∀ u, ENNReal.ofReal (Q u) ≤ ENNReal.ofReal (P u) + ENNReal.ofReal (Mr u) := by
    intro u
    rw [← ENNReal.ofReal_add (hPnn u) (hMnn u)]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (hdiff u)).1])
  -- The roles of the circle and line integrals are exchanged: the circle integral is finite,
  -- so the line integral is finite and the two differ by the weighted cross term.
  obtain ⟨hQfin, hbound⟩ := toReal_sub_le_of_pointwise
    (w := fun u : ℝ => ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹)) hw hQm hPm hMm
    (fun u => by rw [hQe u, hPe u, hMe u]; exact hQPe u)
    (fun u => by rw [hQe u, hPe u, hMe u]; exact hPQe u) hPfin hMfin
  have hLfin : ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
      (∫⁻ η, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * (η * u))) * ‖𝓕 g η‖ ^ 2)) ≠ ⊤ :=
    hQfin
  refine ⟨?_, ?_⟩
  · rw [hB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLfin
  -- The cross-term bound of the shift sum, in the form needed here.
  have hsumnn : 0 ≤ ∑' m : ℤ, shiftCoeff ρ τ m := tsum_nonneg (shiftCoeff_nonneg hρ)
  have hL : ∫⁻ v, ‖autocorr g v‖ₑ ≤ ENNReal.ofReal ((∫ x, ‖g x‖) ^ 2) := by
    calc ∫⁻ v, ‖autocorr g v‖ₑ ≤ (∫⁻ x, ‖g x‖ₑ) ^ 2 := lintegral_enorm_autocorr_le hmeas
      _ = (ENNReal.ofReal (∫ x, ‖g x‖)) ^ 2 := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hg1]
      _ = ENNReal.ofReal ((∫ x, ‖g x‖) ^ 2) :=
          (ENNReal.ofReal_pow (integral_nonneg (fun x => norm_nonneg _)) 2).symm
  have hIM' : ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
      (∑' m : ℤ, ‖(if m = 0 then (0 : ℂ) else autocorr g (u + m))‖ₑ) ≤
      ENNReal.ofReal ((∑' m : ℤ, shiftCoeff ρ τ m) * (∫ x, ‖g x‖) ^ 2) := by
    refine (lintegral_weight_autocorr_tsum_le hρ0 hρ hsupp hmeas hτ).trans ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (shiftCoeff_nonneg hρ) (summable_shiftCoeff hρ hτ),
      ENNReal.ofReal_mul hsumnn]
    gcongr
  have hIM : (∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
      (∑' m : ℤ, ‖(if m = 0 then (0 : ℂ) else autocorr g (u + m))‖ₑ)).toReal ≤
      (∑' m : ℤ, shiftCoeff ρ τ m) * (∫ x, ‖g x‖) ^ 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hIM'
    rwa [ENNReal.toReal_ofReal (mul_nonneg hsumnn (sq_nonneg _))] at h
  -- Assemble: rewrite both seminorms as `κ` times the weighted integrals and apply the bound.
  rw [hA, hB, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hκpos.le]
  exact (abs_const_mul_sub_const_mul_le hκpos.le (hbound.trans hIM)).trans_eq (mul_assoc _ _ _).symm

end Riesz1
