/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.SeminormScaling
public import Riesz1.Kernel.SeminormScalingConverseCore

/-!
# Converse comparison of the circle and line seminorms

Last assertion of the scaling comparison: if the pullback of the periodization of `ξ₀` lies in
`H^{(1-s)/2}(𝕋)`, then the zero extension `ξ₀` lies in `H^{(1-s)/2}(ℝ)`, and the comparison
of `Riesz1.seminorm_scaling` holds with the same constant. The forward comparison assumes that
the line seminorm is finite. Here the circle seminorm is assumed finite instead.

`Riesz1.seminorm_scaling_full` collects both assertions with one constant.
-/

public section

open MeasureTheory Set FourierTransform
open scoped ENNReal ComplexConjugate

namespace Riesz1

/-- **Converse comparison of the circle and line seminorms under rescaling.** For `0 < s < 1`
and `0 < d < 1/2`, there is a constant `C > 0`, depending only on `s` and `d`, such that for every
`0 < ℓ ≤ 1` and every real `L²` profile `ξ₀` supported in `[-(1/2 - d), 1/2 - d]` whose pullback
`ξ(ℓ⁻¹ ·)` lies in `H^{(1-s)/2}(𝕋)`, the profile lies in `H^{(1-s)/2}(ℝ)` and the comparison
holds with the constant `C`. -/
theorem seminorm_scaling_converse {s d : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hd0 : 0 < d)
    (hd1 : d < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℝ) (ξ₀ : ℝ → ℝ) (hL2 : MemLp (fun x => (ξ₀ x : ℂ)) 2 volume),
      0 < ℓ → ℓ ≤ 1 →
      (∀ᵐ x ∂volume, 1 / 2 - d < |x| → ξ₀ x = 0) →
      (∃ hF : MemLp (pullbackPeriodization ξ₀ ℓ) 2 volume,
        circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hF⟩ < ⊤) →
      LineSobolev ((1 - s) / 2) (hL2.toLp _) ∧
        ∃ hF : MemLp (pullbackPeriodization ξ₀ ℓ) 2 volume,
          |(circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hF⟩).toReal -
              ℓ ^ s * (lineSobolevSq ((1 - s) / 2) (hL2.toLp _)).toReal| ≤
            C * ℓ ^ 2 * ∫ x, ξ₀ x ^ 2 := by
  have hτ : 0 < 1 - s := by linarith
  have hτ1 : 1 - s ≤ 1 := by linarith
  have hτ2 : 1 - s < 2 := by linarith
  have hL0 : 0 ≤ 1 / 2 - d := by linarith
  have hL1 : 1 / 2 - d < 1 / 2 := by linarith
  have hSsum : Summable (shiftCoeff (1 / 2 - d) (1 - s)) := summable_shiftCoeff hL1 hτ
  have hSnn : ∀ m : ℤ, 0 ≤ shiftCoeff (1 / 2 - d) (1 - s) m := shiftCoeff_nonneg hL1
  have hpos1 : 0 < shiftCoeff (1 / 2 - d) (1 - s) 1 := by
    unfold shiftCoeff
    apply inv_pos.mpr
    apply Real.rpow_pos_of_pos
    apply mul_pos
    · linarith
    · simp
  have hS : 0 < ∑' m : ℤ, shiftCoeff (1 / 2 - d) (1 - s) m := hSsum.tsum_pos hSnn 1 hpos1
  refine ⟨(levyIntegral (1 - s))⁻¹ * (∑' m : ℤ, shiftCoeff (1 / 2 - d) (1 - s) m) * (1 - 2 * d),
    ?_, ?_⟩
  · have hκ : 0 < (levyIntegral (1 - s))⁻¹ := inv_pos.mpr (levyIntegral_pos hτ hτ1)
    have : 0 < 1 - 2 * d := by linarith
    positivity
  intro ℓ ξ₀ hL2 hℓ hℓ1 hsupp hH
  obtain ⟨hF, hcirc_fin⟩ := hH
  set L : ℝ := 1 / 2 - d with hLdef
  -- A measurable representative, supported in the window `[-L, L]` pointwise.
  set kf : ℝ → ℂ := hL2.aestronglyMeasurable.mk (fun x => (ξ₀ x : ℂ)) with hkf
  have hkf_meas : Measurable kf := hL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hkf_ae : (fun x => (ξ₀ x : ℂ)) =ᵐ[volume] kf := hL2.aestronglyMeasurable.ae_eq_mk
  set ξ : ℝ → ℂ := (Icc (-L) L).indicator kf with hξdef
  have hξmeas : Measurable ξ := hkf_meas.indicator measurableSet_Icc
  have hξsupp : ∀ x, L < |x| → ξ x = 0 := by
    intro x hx
    have hnot : x ∉ Icc (-L) L := fun h => absurd (abs_le.mpr (mem_Icc.mp h)) (not_le.mpr hx)
    exact indicator_of_notMem hnot _
  have hae : (fun x => (ξ₀ x : ℂ)) =ᵐ[volume] ξ := by
    filter_upwards [hkf_ae, hsupp] with x hx1 hx2
    by_cases hxL : |x| ≤ L
    · have hmem : x ∈ Icc (-L) L := mem_Icc.mpr (abs_le.mp hxL)
      rw [hξdef, indicator_of_mem hmem]
      exact hx1
    · have hxL' : L < |x| := not_le.mp hxL
      rw [hξsupp x hxL', hx2 hxL']
      simp
  have hL2' : MemLp ξ 2 volume := MemLp.ae_eq hae hL2
  have hξsupp_sub : Function.support ξ ⊆ Icc (-L) L := by
    intro x hx
    by_contra hn
    apply hx
    have : L < |x| := not_le.mp (fun h => hn (mem_Icc.mpr (abs_le.mp h)))
    exact hξsupp x this
  have hL1' : Integrable ξ :=
    (integrableOn_iff_integrable_of_support_subset hξsupp_sub).mp
      ((hL2'.restrict _).integrable one_le_two)
  have hcont : Continuous (𝓕 ξ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hL1'
  -- Rescaling: the profile `z ↦ ξ(z/ℓ)` is supported in `[-ℓL, ℓL]`.
  have hρ0 : 0 ≤ ℓ * L := mul_nonneg hℓ.le hL0
  have hρ1 : ℓ * L < 1 / 2 := by
    have : ℓ * L ≤ L := mul_le_of_le_one_left hL0 hℓ1
    linarith
  have hgsupp : ∀ z : ℝ, ℓ * L < |z| → (fun z : ℝ => ξ (z / ℓ)) z = 0 := by
    intro z hz
    show ξ (z / ℓ) = 0
    apply hξsupp
    rw [abs_div, abs_of_pos hℓ, lt_div_iff₀ hℓ, mul_comm]
    exact hz
  have hgmeas : Measurable (fun z : ℝ => ξ (z / ℓ)) := hξmeas.comp (measurable_id.div_const ℓ)
  have hgL2 : MemLp (fun z : ℝ => ξ (z / ℓ)) 2 volume := memLp_comp_div hL2' hℓ
  have hgL1 : Integrable (fun z : ℝ => ξ (z / ℓ)) := hL1'.comp_div (ne_of_gt hℓ)
  -- The pullback and its Fourier coefficients agree with those of the rescaled profile.
  have hN : volume {x : ℝ | ¬ ((ξ₀ x : ℂ) = ξ x)} = 0 := ae_iff.mp hae
  have hterm : ∀ᵐ y ∂volume, ∀ n : ℤ, ((ξ₀ ((y + n) / ℓ) : ℝ) : ℂ) = ξ ((y + n) / ℓ) := by
    rw [ae_all_iff]
    intro n
    exact ae_iff.mpr (measure_preimage_div_add_eq_zero hN hℓ n)
  have hGae : ∀ᵐ y ∂volume, (∑' n : ℤ, (ξ₀ ((y + n) / ℓ) : ℂ)) =
      unitPeriodize (fun z : ℝ => ξ (z / ℓ)) y := by
    filter_upwards [hterm] with y hy
    unfold unitPeriodize
    exact tsum_congr (fun n => hy n)
  have hGres : (fun y : ℝ => ∑' n : ℤ, (ξ₀ ((y + n) / ℓ) : ℂ)) =ᵐ[volume.restrict
      (Ioc (-(1 / 2 : ℝ)) (1 / 2))] unitPeriodize (fun z : ℝ => ξ (z / ℓ)) :=
    ae_restrict_of_ae hGae
  have hc : ∀ k : ℤ, fourierCoeff (pullbackPeriodization ξ₀ ℓ) k =
      𝓕 (fun z : ℝ => ξ (z / ℓ)) (k : ℝ) := by
    intro k
    unfold pullbackPeriodization
    rw [fourierCoeff_liftIoc_cell,
      fourierCoeffOn_congr_ae (show (-(1 / 2 : ℝ)) < 1 / 2 by norm_num) hGres,
      fourierCoeffOn_unitPeriodize hρ1 hgsupp k]
  have hcirc : circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hF⟩ =
      ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) *
        ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) (k : ℝ)‖ ^ 2) :=
    circleSobolevSq_eq_tsum (by ring) hτ hF hc
  have hcirc_ne : ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) *
      ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) (k : ℝ)‖ ^ 2) ≠ ⊤ := by
    rw [← hcirc]
    exact hcirc_fin.ne
  -- The core converse: finite circle seminorm gives finite line seminorm and the comparison.
  obtain ⟨hline_ne, hbd⟩ := seminorm_core_converse hτ hτ1 hρ0 hρ1 hgmeas hgL1 hgL2 hgsupp
    hcirc_ne
  -- The line side and its rescaling.
  have hteq : hL2.toLp (fun x => (ξ₀ x : ℂ)) = hL2'.toLp ξ := MemLp.toLp_congr hL2 hL2' hae
  have hline_eq : lineSobolevSq ((1 - s) / 2) (hL2.toLp (fun x => (ξ₀ x : ℂ))) =
      ∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 ξ η‖ ^ 2) := by
    rw [hteq, lineSobolevSq_toLp_eq_lintegral hL1' hL2', show 2 * ((1 - s) / 2) = 1 - s by ring]
  have hBg : ∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) η‖ ^ 2) =
      ENNReal.ofReal (ℓ ^ s) * ∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 ξ η‖ ^ 2) := by
    rw [lintegral_line_seminorm_rescale hτ2 hcont hℓ, show (1 : ℝ) - (1 - s) = s by ring]
  have hBgreal : (∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) η‖ ^ 2)).toReal =
      ℓ ^ s * (∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 ξ η‖ ^ 2)).toReal := by
    rw [hBg, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hℓ.le _)]
  -- The line seminorm of `ξ` is finite, since that of its rescaling is.
  have hXfin : ∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 ξ η‖ ^ 2) ≠ ⊤ := by
    intro htop
    apply hline_ne
    rw [hBg, htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hℓ s)).ne']
  have hLS : LineSobolev ((1 - s) / 2) (hL2.toLp (fun x => (ξ₀ x : ℂ))) := by
    unfold LineSobolev
    rw [hline_eq]
    exact lt_top_iff_ne_top.mpr hXfin
  refine ⟨hLS, hF, ?_⟩
  rw [hcirc, hline_eq, ← hBgreal]
  -- The `L¹` and `L²` norms of the rescaled profile.
  have hSρ : ∑' m : ℤ, shiftCoeff (ℓ * L) (1 - s) m ≤ ∑' m : ℤ, shiftCoeff L (1 - s) m :=
    (summable_shiftCoeff hρ1 hτ).tsum_le_tsum
      (fun m => shiftCoeff_mono hτ.le (mul_le_of_le_one_left hL0 hℓ1) (by linarith) m) hSsum
  have hgn : ∫ x, ‖ξ (x / ℓ)‖ = ℓ * ∫ x, ‖ξ x‖ := integral_norm_rescale ξ hℓ
  have hsq : (∫ x, ‖ξ x‖) ^ 2 ≤ (2 * L) * ∫ x, ‖ξ x‖ ^ 2 := integral_norm_sq_le hL0 hL2' hξsupp
  have hξ2 : ∫ x, ‖ξ x‖ ^ 2 = ∫ x, ξ₀ x ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [← hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hgsq : (∫ x, ‖ξ (x / ℓ)‖) ^ 2 ≤ ℓ ^ 2 * ((1 - 2 * d) * ∫ x, ξ₀ x ^ 2) := by
    rw [hgn, mul_pow, ← hξ2]
    have h2L : 2 * L = 1 - 2 * d := by rw [hLdef]; ring
    rw [← h2L]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg ℓ)
  have hκ : 0 < (levyIntegral (1 - s))⁻¹ := inv_pos.mpr (levyIntegral_pos hτ hτ1)
  have hSnn' : 0 ≤ ∑' m : ℤ, shiftCoeff L (1 - s) m := tsum_nonneg hSnn
  have hsqnn : 0 ≤ (∫ x, ‖ξ (x / ℓ)‖) ^ 2 := sq_nonneg _
  calc |(∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) *
          ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) (k : ℝ)‖ ^ 2)).toReal -
        (∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) η‖ ^ 2)).toReal|
      ≤ (levyIntegral (1 - s))⁻¹ * (∑' m : ℤ, shiftCoeff (ℓ * L) (1 - s) m) *
          (∫ x, ‖ξ (x / ℓ)‖) ^ 2 := hbd
    _ ≤ (levyIntegral (1 - s))⁻¹ * (∑' m : ℤ, shiftCoeff L (1 - s) m) *
          (ℓ ^ 2 * ((1 - 2 * d) * ∫ x, ξ₀ x ^ 2)) := by
        apply mul_le_mul _ hgsq hsqnn (by positivity)
        exact mul_le_mul_of_nonneg_left hSρ hκ.le
    _ = (levyIntegral (1 - s))⁻¹ * (∑' m : ℤ, shiftCoeff L (1 - s) m) * (1 - 2 * d) *
          ℓ ^ 2 * ∫ x, ξ₀ x ^ 2 := by ring

/-- **Comparison of the circle and line seminorms, both directions.** There is one constant `C > 0`
such that for every `0 < ℓ ≤ 1` and every real `L²` profile `ξ₀` supported in
`[-(1/2 - d), 1/2 - d]`:

* if the zero extension `ξ₀` lies in `H^{(1-s)/2}(ℝ)`, then the pullback of the periodization
  lies in `H^{(1-s)/2}(𝕋)` and the comparison holds.
* if the pullback lies in `H^{(1-s)/2}(𝕋)`, then `ξ₀` lies in `H^{(1-s)/2}(ℝ)` and the
  comparison holds.

This is the statement of the scaling comparison, both of its assertions. -/
theorem seminorm_scaling_full {s d : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hd0 : 0 < d)
    (hd1 : d < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℝ) (ξ₀ : ℝ → ℝ) (hL2 : MemLp (fun x => (ξ₀ x : ℂ)) 2 volume),
      0 < ℓ → ℓ ≤ 1 →
      (∀ᵐ x ∂volume, 1 / 2 - d < |x| → ξ₀ x = 0) →
      (LineSobolev ((1 - s) / 2) (hL2.toLp _) →
        ∃ hF : MemLp (pullbackPeriodization ξ₀ ℓ) 2 volume,
          circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hF⟩ < ⊤ ∧
          |(circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hF⟩).toReal -
              ℓ ^ s * (lineSobolevSq ((1 - s) / 2) (hL2.toLp _)).toReal| ≤
            C * ℓ ^ 2 * ∫ x, ξ₀ x ^ 2) ∧
      ((∃ hF : MemLp (pullbackPeriodization ξ₀ ℓ) 2 volume,
          circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hF⟩ < ⊤) →
        LineSobolev ((1 - s) / 2) (hL2.toLp _) ∧
          ∃ hF : MemLp (pullbackPeriodization ξ₀ ℓ) 2 volume,
            |(circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hF⟩).toReal -
                ℓ ^ s * (lineSobolevSq ((1 - s) / 2) (hL2.toLp _)).toReal| ≤
              C * ℓ ^ 2 * ∫ x, ξ₀ x ^ 2) := by
  obtain ⟨C₁, hC₁, hfwd⟩ := seminorm_scaling hs0 hs1 hd0 hd1
  obtain ⟨C₂, hC₂, hconv⟩ := seminorm_scaling_converse hs0 hs1 hd0 hd1
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun ℓ ξ₀ hL2 hℓ hℓ1 hsupp => ⟨fun hH => ?_, fun hH => ?_⟩⟩
  · obtain ⟨hF, hfin, hb⟩ := hfwd ℓ ξ₀ hL2 hℓ hℓ1 hsupp hH
    refine ⟨hF, hfin, hb.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ℓ))
      (integral_nonneg (fun x => sq_nonneg _))
  · obtain ⟨hline, hF, hb⟩ := hconv ℓ ξ₀ hL2 hℓ hℓ1 hsupp hH
    refine ⟨hline, hF, hb.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg ℓ))
      (integral_nonneg (fun x => sq_nonneg _))

end Riesz1
