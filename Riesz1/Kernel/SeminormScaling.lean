/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.SeminormScalingRescale
public import Riesz1.Frozen.CircleSobolevSq
public import Riesz1.Frozen.LineSobolevSq
public import Riesz1.Frozen.LineSobolev

/-!
# Comparison of the circle and line seminorms under rescaling

For `ℓ ∈ (0, 1]` and an `L²` profile `ξ₀` supported in `[-(1/2 - d), 1/2 - d]`, the circle
seminorm of the pullback of the periodization of `ξ₀` with period `1/ℓ` differs from `ℓ^s` times
the line seminorm of `ξ₀` by at most a constant times `ℓ² ‖ξ₀‖₂²`.
-/

public section

open MeasureTheory Set FourierTransform
open scoped ENNReal ComplexConjugate

namespace Riesz1

/-- The pullback to the unit circle of the periodization of `ξ₀` with period `1/ℓ`: the function
`x ↦ ∑_{n ∈ ℤ} ξ₀((x + n)/ℓ)`, which is `ξ(ℓ⁻¹ ·)` for `ξ(u) = ∑_{n} ξ₀(u + n/ℓ)`. -/
@[expose]
noncomputable def pullbackPeriodization (ξ₀ : ℝ → ℝ) (ℓ : ℝ) : UnitAddCircle → ℂ :=
  AddCircle.liftIoc 1 (-(1 / 2 : ℝ)) (fun x => ∑' n : ℤ, (ξ₀ ((x + n) / ℓ) : ℂ))

/-- Affine rescaling of a null set is null: the preimage of a null set under `y ↦ (y + n)/ℓ`. -/
theorem measure_preimage_div_add_eq_zero {N : Set ℝ} (hN : volume N = 0) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (n : ℤ) : volume ((fun y : ℝ => (y + (n : ℝ)) / ℓ) ⁻¹' N) = 0 := by
  have h1 : (fun y : ℝ => (y + (n : ℝ)) / ℓ) ⁻¹' N =
      (fun y : ℝ => y + (n : ℝ)) ⁻¹' ((fun x : ℝ => ℓ⁻¹ * x) ⁻¹' N) := by
    ext y
    simp [div_eq_inv_mul]
  rw [h1, measure_preimage_add_right, Real.volume_preimage_mul_left (inv_ne_zero hℓ.ne'), hN,
    mul_zero]

/-- The shift coefficients increase with the support radius. -/
theorem shiftCoeff_mono {ρ ρ' τ : ℝ} (hτ : 0 ≤ τ) (hρρ' : ρ ≤ ρ')
    (hρ' : ρ' < 1 / 2) (m : ℤ) :
    shiftCoeff ρ τ m ≤ shiftCoeff ρ' τ m := by
  unfold shiftCoeff
  by_cases hm : m = 0
  · simp [hm]
  have hmpos : (0 : ℝ) < |(m : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hm)
  have hpos : 0 < (1 - 2 * ρ') * |(m : ℝ)| := mul_pos (by linarith) hmpos
  have hle : (1 - 2 * ρ') * |(m : ℝ)| ≤ (1 - 2 * ρ) * |(m : ℝ)| :=
    mul_le_mul_of_nonneg_right (by linarith) hmpos.le
  exact inv_anti₀ (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hle (by linarith))

/-- The unit-circle Fourier coefficients of the pullback are the cell Fourier coefficients of the
periodization. -/
theorem fourierCoeff_liftIoc_cell (G : ℝ → ℂ) (k : ℤ) :
    fourierCoeff (AddCircle.liftIoc 1 (-(1 / 2 : ℝ)) G) k =
      fourierCoeffOn (show (-(1 / 2 : ℝ)) < 1 / 2 by norm_num) G k := by
  rw [fourierCoeff_liftIoc_eq]
  simp only [fourierCoeffOn_eq_integral, fourier_coe_apply]
  norm_num

/-- Dilation of an `L²` function is `L²`. -/
theorem memLp_comp_div {f : ℝ → ℂ} (hf : MemLp f 2 volume) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MemLp (fun z => f (z / ℓ)) 2 volume := by
  have hmap : Measure.map (fun z : ℝ => z / ℓ) volume = ENNReal.ofReal ℓ • volume := by
    have h : (fun z : ℝ => z / ℓ) = fun z : ℝ => ℓ⁻¹ * z := by
      funext z
      rw [div_eq_inv_mul]
    rw [h, Real.map_volume_mul_left (inv_ne_zero hℓ.ne'), inv_inv, abs_of_pos hℓ]
  have hf' : MemLp f 2 (Measure.map (fun z : ℝ => z / ℓ) volume) := by
    rw [hmap]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hf'.comp_of_map (measurable_id.div_const ℓ).aemeasurable

/-- The circle Sobolev seminorm of a function with prescribed Fourier coefficients. -/
theorem circleSobolevSq_eq_tsum {r τ : ℝ} (hr : 2 * r = τ) (hτ : 0 < τ) {F : UnitAddCircle → ℂ}
    (hF : MemLp F 2 volume) {g : ℝ → ℂ} (hc : ∀ k : ℤ, fourierCoeff F k = 𝓕 g (k : ℝ)) :
    circleSobolevSq r ⟨F, hF⟩ = ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ τ * ‖𝓕 g (k : ℝ)‖ ^ 2) := by
  unfold circleSobolevSq
  congr 1
  funext k
  by_cases hk : k = 0
  · subst hk
    simp only [ite_true, Int.cast_zero, abs_zero]
    rw [Real.zero_rpow hτ.ne', zero_mul, ENNReal.ofReal_zero]
  · rw [ite_eq_right hk, hc k, ← hr]

/-- The line seminorm of an `L²` representative is the integral form. -/
theorem lineSobolevSq_toLp_eq_lintegral {r : ℝ} {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume) :
    lineSobolevSq r (hf2.toLp f) = ∫⁻ η, ENNReal.ofReal (|η| ^ (2 * r) * ‖𝓕 f η‖ ^ 2) := by
  unfold lineSobolevSq
  apply lintegral_congr_ae
  filter_upwards [fourier_toLp_ae hf1 hf2] with η hη
  rw [show Lp.fourierTransformₗᵢ ℝ ℂ (hf2.toLp f) η = 𝓕 f η from hη]

/-- **Comparison of the circle and line seminorms under rescaling.** -/
theorem seminorm_scaling {s d : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hd0 : 0 < d) (hd1 : d < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℝ) (ξ₀ : ℝ → ℝ) (hL2 : MemLp (fun x => (ξ₀ x : ℂ)) 2 volume),
      0 < ℓ → ℓ ≤ 1 →
      (∀ᵐ x ∂volume, 1 / 2 - d < |x| → ξ₀ x = 0) →
      LineSobolev ((1 - s) / 2) (hL2.toLp _) →
      ∃ hF : MemLp (pullbackPeriodization ξ₀ ℓ) 2 volume,
        circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hF⟩ < ⊤ ∧
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
  have hL1 : Integrable ξ :=
    (integrableOn_iff_integrable_of_support_subset hξsupp_sub).mp
      ((hL2'.restrict _).integrable one_le_two)
  have hcont : Continuous (𝓕 ξ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hL1
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
  have hgL1 : Integrable (fun z : ℝ => ξ (z / ℓ)) := hL1.comp_div (ne_of_gt hℓ)
  -- The line seminorm of the rescaled profile is finite.
  have hline : ∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) η‖ ^ 2) ≠ ⊤ := by
    rw [lintegral_line_seminorm_rescale hτ2 hcont hℓ, show (1 : ℝ) - (1 - s) = s by ring]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have hteq : hL2.toLp (fun x => (ξ₀ x : ℂ)) = hL2'.toLp ξ := MemLp.toLp_congr hL2 hL2' hae
    have hH' : lineSobolevSq ((1 - s) / 2) (hL2.toLp (fun x => (ξ₀ x : ℂ))) < ⊤ := hH
    rw [hteq, lineSobolevSq_toLp_eq_lintegral hL1 hL2', show 2 * ((1 - s) / 2) = 1 - s by ring] at hH'
    exact hH'.ne
  -- The core comparison.
  obtain ⟨hAfin, hbd⟩ := seminorm_core_bound hτ hτ1 hρ0 hρ1 hgmeas hgL1 hgL2 hgsupp hline
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
  have hcell_L2 : MemLp (unitPeriodize (fun z : ℝ => ξ (z / ℓ))) 2
      (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) :=
    memLp_unitPeriodize_cell hρ1 hgsupp hgL2
  have hGL2 : MemLp (fun y : ℝ => ∑' n : ℤ, (ξ₀ ((y + n) / ℓ) : ℂ)) 2
      (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) := MemLp.ae_eq hGres.symm hcell_L2
  have hFL2 : MemLp (pullbackPeriodization ξ₀ ℓ) 2 volume := by
    unfold pullbackPeriodization
    have hcell' : MemLp (fun y : ℝ => ∑' n : ℤ, (ξ₀ ((y + n) / ℓ) : ℂ)) 2
        (volume.restrict (Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1))) := by
      rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
      exact hGL2
    exact hcell'.memLp_liftIoc
  have hc : ∀ k : ℤ, fourierCoeff (pullbackPeriodization ξ₀ ℓ) k =
      𝓕 (fun z : ℝ => ξ (z / ℓ)) (k : ℝ) := by
    intro k
    unfold pullbackPeriodization
    rw [fourierCoeff_liftIoc_cell,
      fourierCoeffOn_congr_ae (show (-(1 / 2 : ℝ)) < 1 / 2 by norm_num) hGres,
      fourierCoeffOn_unitPeriodize hρ1 hgsupp k]
  have hcirc : circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hFL2⟩ =
      ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| ^ (1 - s) *
        ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) (k : ℝ)‖ ^ 2) :=
    circleSobolevSq_eq_tsum (by ring) hτ hFL2 hc
  have hcirc_fin : circleSobolevSq ((1 - s) / 2) ⟨pullbackPeriodization ξ₀ ℓ, hFL2⟩ < ⊤ := by
    rw [hcirc]
    exact lt_top_iff_ne_top.mpr hAfin
  refine ⟨hFL2, hcirc_fin, ?_⟩
  -- The line side and its rescaling.
  have hteq : hL2.toLp (fun x => (ξ₀ x : ℂ)) = hL2'.toLp ξ := MemLp.toLp_congr hL2 hL2' hae
  have hline_eq : lineSobolevSq ((1 - s) / 2) (hL2.toLp (fun x => (ξ₀ x : ℂ))) =
      ∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 ξ η‖ ^ 2) := by
    rw [hteq, lineSobolevSq_toLp_eq_lintegral hL1 hL2', show 2 * ((1 - s) / 2) = 1 - s by ring]
  have hBg : ∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) η‖ ^ 2) =
      ENNReal.ofReal (ℓ ^ s) * ∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 ξ η‖ ^ 2) := by
    rw [lintegral_line_seminorm_rescale hτ2 hcont hℓ, show (1 : ℝ) - (1 - s) = s by ring]
  have hBgreal : (∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 (fun z : ℝ => ξ (z / ℓ)) η‖ ^ 2)).toReal =
      ℓ ^ s * (∫⁻ η, ENNReal.ofReal (|η| ^ (1 - s) * ‖𝓕 ξ η‖ ^ 2)).toReal := by
    rw [hBg, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hℓ.le _)]
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
  have hSnn : 0 ≤ ∑' m : ℤ, shiftCoeff L (1 - s) m := tsum_nonneg hSnn
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

end Riesz1
