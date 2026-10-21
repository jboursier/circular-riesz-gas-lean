/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.SeminormScalingCross
public import Riesz1.Kernel.SeminormScalingKernel

/-!
# The core seminorm comparison

The circle and line seminorms with weight `|η|^τ` are rewritten, through the Lévy
representation, as integrals over the shift variable `u` of the circle and line increments.
Their difference is controlled by the cross terms of `SeminormScalingCross`.
-/

public section

open MeasureTheory Set FourierTransform
open scoped ENNReal ComplexConjugate

namespace Riesz1

/-- The numerator `1 - cos(2π x)` is nonnegative. -/
private lemma one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos (2 * Real.pi * x) := by
  linarith [Real.cos_le_one (2 * Real.pi * x)]

/-- The Lévy representation in `ENNReal` form: the weighted seminorm term at frequency `η`
is the Lévy constant times the integral over the shift of the weight times `1 - cos`. -/
theorem ofReal_rpow_abs_mul_eq {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (η c : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal (|η| ^ τ * c) = ENNReal.ofReal (levyIntegral τ)⁻¹ *
      ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
        ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * (η * u))) * c) := by
  have hI : 0 < levyIntegral τ := levyIntegral_pos hτ hτ1
  have hrep := rpow_abs_eq_levy_integral hτ hτ1 η
  have hint : Integrable (fun u : ℝ => (1 - Real.cos (2 * Real.pi * (η * u))) / |u| ^ (1 + τ) * c) :=
    (integrable_levy_scaled hτ hτ1 η).mul_const c
  have hnn : 0 ≤ᵐ[volume] (fun u : ℝ => (1 - Real.cos (2 * Real.pi * (η * u))) / |u| ^ (1 + τ) * c) :=
    ae_of_all _ (fun u => mul_nonneg (div_nonneg (one_sub_cos_nonneg _)
      (Real.rpow_nonneg (abs_nonneg u) _)) hc)
  have e1 : |η| ^ τ * c = (levyIntegral τ)⁻¹ *
      ∫ u : ℝ, (1 - Real.cos (2 * Real.pi * (η * u))) / |u| ^ (1 + τ) * c := by
    rw [integral_mul_const, hrep]
    ring
  rw [e1, ENNReal.ofReal_mul (inv_nonneg.mpr hI.le),
    ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  refine lintegral_congr (fun u => ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The circle seminorm as an integral over the shift variable of the weight times the sum of
the circle increments. -/
theorem circle_seminorm_eq_lintegral {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (g : ℝ → ℂ) :
    ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ τ * ‖𝓕 g (k : ℝ)‖ ^ 2) =
      ENNReal.ofReal (levyIntegral τ)⁻¹ * ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
        ∑' k : ℤ, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) * ‖𝓕 g (k : ℝ)‖ ^ 2) := by
  have hstep : ∀ k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ τ * ‖𝓕 g (k : ℝ)‖ ^ 2) =
      ENNReal.ofReal (levyIntegral τ)⁻¹ * ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
        ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) * ‖𝓕 g (k : ℝ)‖ ^ 2) :=
    fun k => ofReal_rpow_abs_mul_eq hτ hτ1 (k : ℝ) (‖𝓕 g (k : ℝ)‖ ^ 2) (by positivity)
  rw [tsum_congr hstep, ENNReal.tsum_mul_left, ← lintegral_tsum]
  · congr 1
    refine lintegral_congr (fun u => ?_)
    rw [ENNReal.tsum_mul_left]
  · intro k
    refine Measurable.aemeasurable ?_
    have hw : Measurable (fun u : ℝ => ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹)) := by fun_prop
    exact hw.mul (by fun_prop)

/-- The line seminorm as an integral over the shift variable of the weight times the line
increment kernel. -/
theorem line_seminorm_eq_lintegral {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {g : ℝ → ℂ}
    (hcont : Continuous (𝓕 g)) :
    ∫⁻ η, ENNReal.ofReal (|η| ^ τ * ‖𝓕 g η‖ ^ 2) =
      ENNReal.ofReal (levyIntegral τ)⁻¹ * ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
        ∫⁻ η, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * (η * u))) * ‖𝓕 g η‖ ^ 2) := by
  have hm : Measurable (𝓕 g) := hcont.measurable
  have hpt : ∀ η : ℝ, ENNReal.ofReal (|η| ^ τ * ‖𝓕 g η‖ ^ 2) =
      ENNReal.ofReal (levyIntegral τ)⁻¹ * ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
        ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * (η * u))) * ‖𝓕 g η‖ ^ 2) :=
    fun η => ofReal_rpow_abs_mul_eq hτ hτ1 η _ (by positivity)
  have hjoint : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((|p.2| ^ (1 + τ))⁻¹) *
      ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * (p.1 * p.2))) * ‖𝓕 g p.1‖ ^ 2)) := by
    fun_prop
  rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_lintegral_swap (hjoint.aemeasurable)]
  refine lintegral_congr (fun u => ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Real part form of a pointwise domination: if `P ≤ Q + M` and `Q ≤ P + M` pointwise, the
weighted integrals of `P` and `Q` differ by at most the weighted integral of `M`. -/
theorem toReal_sub_le_of_pointwise {w P Q M : ℝ → ℝ≥0∞} (hw : Measurable w) (hP : Measurable P)
    (hQ : Measurable Q) (hM : Measurable M) (hPQ : ∀ u, P u ≤ Q u + M u)
    (hQP : ∀ u, Q u ≤ P u + M u) (hQfin : ∫⁻ u, w u * Q u ≠ ⊤) (hMfin : ∫⁻ u, w u * M u ≠ ⊤) :
    ∫⁻ u, w u * P u ≠ ⊤ ∧
      |(∫⁻ u, w u * P u).toReal - (∫⁻ u, w u * Q u).toReal| ≤ (∫⁻ u, w u * M u).toReal := by
  have hwQ : Measurable (fun u => w u * Q u) := hw.mul hQ
  have hwM : Measurable (fun u => w u * M u) := hw.mul hM
  have hwP : Measurable (fun u => w u * P u) := hw.mul hP
  have hsum1 : ∫⁻ u, w u * P u ≤ ∫⁻ u, (w u * Q u + w u * M u) := by
    refine lintegral_mono (fun u => ?_)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hPQ u) zero_le
  have hsum2 : ∫⁻ u, w u * Q u ≤ ∫⁻ u, (w u * P u + w u * M u) := by
    refine lintegral_mono (fun u => ?_)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hQP u) zero_le
  rw [lintegral_add_left' hwQ.aemeasurable] at hsum1
  rw [lintegral_add_left' hwP.aemeasurable] at hsum2
  have hPfin : ∫⁻ u, w u * P u ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hsum1
    exact ENNReal.add_ne_top.mpr ⟨hQfin, hMfin⟩
  refine ⟨hPfin, ?_⟩
  have hb : (∫⁻ u, w u * Q u) + (∫⁻ u, w u * M u) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hQfin, hMfin⟩
  have ha : (∫⁻ u, w u * P u) + (∫⁻ u, w u * M u) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hPfin, hMfin⟩
  have h1 : (∫⁻ u, w u * P u).toReal ≤ (∫⁻ u, w u * Q u).toReal + (∫⁻ u, w u * M u).toReal := by
    rw [← ENNReal.toReal_add hQfin hMfin]
    exact ENNReal.toReal_mono hb hsum1
  have h2 : (∫⁻ u, w u * Q u).toReal ≤ (∫⁻ u, w u * P u).toReal + (∫⁻ u, w u * M u).toReal := by
    rw [← ENNReal.toReal_add hPfin hMfin]
    exact ENNReal.toReal_mono ha hsum2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The shift coefficients are nonnegative. -/
theorem shiftCoeff_nonneg {ρ τ : ℝ} (hρ : ρ < 1 / 2) (m : ℤ) : 0 ≤ shiftCoeff ρ τ m := by
  unfold shiftCoeff
  apply inv_nonneg.mpr
  apply Real.rpow_nonneg
  apply mul_nonneg
  · linarith
  · exact abs_nonneg _

/-- **Core seminorm comparison.** For a function supported in `[-ρ, ρ]` with `ρ < 1/2` and
finite line seminorm, the circle seminorm is finite and differs from the line seminorm by at
most a constant times the squared `L¹` norm. -/
theorem seminorm_core_bound {τ ρ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2)
    {g : ℝ → ℂ} (hmeas : Measurable g) (hg1 : Integrable g) (hg2 : MemLp g 2 volume)
    (hsupp : ∀ x : ℝ, ρ < |x| → g x = 0)
    (hline : ∫⁻ η, ENNReal.ofReal (|η| ^ τ * ‖𝓕 g η‖ ^ 2) ≠ ⊤) :
    ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ τ * ‖𝓕 g (k : ℝ)‖ ^ 2) ≠ ⊤ ∧
      |(∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ τ * ‖𝓕 g (k : ℝ)‖ ^ 2)).toReal -
          (∫⁻ η, ENNReal.ofReal (|η| ^ τ * ‖𝓕 g η‖ ^ 2)).toReal| ≤
        (levyIntegral τ)⁻¹ * (∑' m : ℤ, shiftCoeff ρ τ m) * (∫ x, ‖g x‖) ^ 2 := by
  have hcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg1
  have hκpos : 0 < (levyIntegral τ)⁻¹ := inv_pos.mpr (levyIntegral_pos hτ hτ1)
  have hA := circle_seminorm_eq_lintegral hτ hτ1 g
  have hB := line_seminorm_eq_lintegral hτ hτ1 hcont
  -- Real-valued and extended-valued pieces of the cross-term decomposition.
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
  -- Finiteness of the weighted pieces.
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
  have hQfin : ∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) * (∫⁻ η, ENNReal.ofReal
      ((1 - Real.cos (2 * Real.pi * (η * u))) * ‖𝓕 g η‖ ^ 2)) ≠ ⊤ := by
    intro htop
    apply hline
    rw [hB, htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hκpos).ne']
  -- Pointwise domination in the extended values.
  have hPQe : ∀ u, ENNReal.ofReal (P u) ≤ ENNReal.ofReal (Q u) + ENNReal.ofReal (Mr u) := by
    intro u
    rw [← ENNReal.ofReal_add (hQnn u) (hMnn u)]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (hdiff u)).2])
  have hQPe : ∀ u, ENNReal.ofReal (Q u) ≤ ENNReal.ofReal (P u) + ENNReal.ofReal (Mr u) := by
    intro u
    rw [← ENNReal.ofReal_add (hPnn u) (hMnn u)]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (hdiff u)).1])
  obtain ⟨hPfin, hbound⟩ := toReal_sub_le_of_pointwise (w := fun u : ℝ =>
      ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹)) hw hPm hQm hMm
    (fun u => by rw [hPe u, hQe u, hMe u]; exact hPQe u)
    (fun u => by rw [hPe u, hQe u, hMe u]; exact hQPe u) hQfin hMfin
  -- The circle seminorm is finite.
  have hA_fin : ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ τ * ‖𝓕 g (k : ℝ)‖ ^ 2) ≠ ⊤ := by
    rw [hA]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPfin
  refine ⟨hA_fin, ?_⟩
  -- The cross-term constant of the shifted sum.
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
  rw [hA, hB, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hκpos.le]
  calc |(levyIntegral τ)⁻¹ * (∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
          ∑' k : ℤ, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) *
            ‖𝓕 g (k : ℝ)‖ ^ 2)).toReal -
        (levyIntegral τ)⁻¹ * (∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
          (∫⁻ η, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * (η * u))) * ‖𝓕 g η‖ ^ 2))).toReal|
      = (levyIntegral τ)⁻¹ * |(∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
          ∑' k : ℤ, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * ((k : ℝ) * u))) *
            ‖𝓕 g (k : ℝ)‖ ^ 2)).toReal -
        (∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
          (∫⁻ η, ENNReal.ofReal ((1 - Real.cos (2 * Real.pi * (η * u))) * ‖𝓕 g η‖ ^ 2))).toReal| := by
        rw [← mul_sub, abs_mul, abs_of_pos hκpos]
    _ ≤ (levyIntegral τ)⁻¹ * (∫⁻ u, ENNReal.ofReal ((|u| ^ (1 + τ))⁻¹) *
          (∑' m : ℤ, ‖(if m = 0 then (0 : ℂ) else autocorr g (u + m))‖ₑ)).toReal :=
        mul_le_mul_of_nonneg_left (by simpa only [] using hbound) hκpos.le
    _ ≤ (levyIntegral τ)⁻¹ * ((∑' m : ℤ, shiftCoeff ρ τ m) * (∫ x, ‖g x‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hIM hκpos.le
    _ = (levyIntegral τ)⁻¹ * (∑' m : ℤ, shiftCoeff ρ τ m) * (∫ x, ‖g x‖) ^ 2 := by ring

end Riesz1
