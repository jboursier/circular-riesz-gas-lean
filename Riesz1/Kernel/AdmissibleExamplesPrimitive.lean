/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesPowerSobolev
public import Riesz1.Frozen.PrimitiveRegularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Hölder primitives from Fourier coefficient decay

A weighted absolutely convergent Fourier series is Hölder continuous. Applied to
coefficients divided by the nonzero frequency, this constructs periodic primitives.
-/

public section

open MeasureTheory Set Filter Topology ComplexConjugate

namespace Riesz1
namespace Internal

lemma norm_fourier_sub_le_frequency (k : ℤ) (x y : UnitAddCircle) :
    ‖fourier k x - fourier k y‖ ≤ 2 * Real.pi * |(k : ℝ)| * dist x y := by
  obtain ⟨t, ht⟩ := exists_real_coe (x - y)
  let z := t - round t
  have hz : (z : UnitAddCircle) = x - y := by
    dsimp [z]
    rw [show ((round t : ℝ) : UnitAddCircle) = 0 from
      (AddCircle.coe_eq_zero_iff 1).mpr ⟨round t, by simp⟩, sub_zero, ht]
  have hdist : |z| = dist x y := by
    rw [dist_eq_norm, ← ht, UnitAddCircle.norm_eq]
  have he : fourier k x - fourier k y = (fourier k (z : UnitAddCircle) - 1) * fourier k y := by
    rw [hz, sub_mul, one_mul, ← fourier_add_point, sub_add_cancel]
  rw [he, norm_mul, norm_fourier_point, mul_one, fourier_coe_apply]
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (k : ℝ) * z)
  have heq : (2 * Real.pi * Complex.I * (k : ℂ) * (z : ℂ) / (1 : ℂ)) =
      Complex.I * ((2 * Real.pi * (k : ℝ) * z : ℝ) : ℂ) := by push_cast; ring
  simp only [Complex.ofReal_one, heq]
  convert hb using 1
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos), hdist]

lemma norm_fourier_sub_le_holder (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (k : ℤ) (x y : UnitAddCircle) :
    ‖fourier k x - fourier k y‖ ≤
      2 * (2 * Real.pi * |(k : ℝ)|) ^ r * dist x y ^ r := by
  let t := 2 * Real.pi * |(k : ℝ)| * dist x y
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsmall := norm_fourier_sub_le_frequency k x y
  have hlarge : ‖fourier k x - fourier k y‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by rw [norm_fourier_point, norm_fourier_point]; norm_num)
  have hb : ‖fourier k x - fourier k y‖ ≤ 2 * t ^ r := by
    by_cases ht0 : t = 0
    · have hh : ‖fourier k x - fourier k y‖ ≤ 0 := by simpa [t, ht0] using hsmall
      simpa [ht0, Real.zero_rpow hr0.ne'] using hh
    · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      by_cases ht1 : t ≤ 1
      · have hh : t ≤ t ^ r := by
          simpa using Real.rpow_le_rpow_of_exponent_ge htp ht1 hr1
        have hp : 0 ≤ t ^ r := Real.rpow_nonneg ht r
        exact hsmall.trans (by change t ≤ 2 * t ^ r; linarith)
      · exact hlarge.trans (by nlinarith [Real.one_le_rpow (le_of_not_ge ht1) hr0.le])
  dsimp only [t] at hb
  rw [Real.mul_rpow (by positivity : 0 ≤ 2 * Real.pi * |(k : ℝ)|) dist_nonneg] at hb
  simpa only [mul_assoc] using hb

/-- An absolutely convergent conjugate-symmetric Fourier series with a summable frequency
weight has a real Hölder representative and the prescribed coefficients. -/
lemma exists_real_holder_fourierSeries {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (c : ℤ → ℂ) (hc : Summable fun k => ‖c k‖)
    (hsym : ∀ k, conj (c k) = c (-k))
    (hw : Summable fun k => 2 * ‖c k‖ * (2 * Real.pi * |(k : ℝ)|) ^ r) :
    ∃ G : UnitAddCircle → ℝ, Continuous G ∧
      (∀ k, fourierCoeff (fun x => (G x : ℂ)) k = c k) ∧
      ∃ B : ℝ, 0 < B ∧ (∀ x, |G x| ≤ B) ∧
        ∀ x y, |G x - G y| ≤ B * dist x y ^ r := by
  let F : UnitAddCircle → ℂ := fun x => ∑' k : ℤ, c k * fourier k x
  have hFc : Continuous F := continuous_tsum
    (fun k => continuous_const.mul (fourier k).continuous) hc
    (fun k x => by rw [norm_mul, norm_fourier_point, mul_one])
  have hreal : ∀ x, ((F x).re : ℂ) = F x := by
    intro x
    apply Complex.conj_eq_iff_re.mp
    dsimp only [F]
    rw [Complex.conj_tsum]
    calc
      ∑' k : ℤ, conj (c k * fourier k x) = ∑' k : ℤ, c (-k) * fourier (-k) x := by
        apply tsum_congr
        intro k
        rw [map_mul, hsym, ← fourier_neg]
      _ = ∑' k : ℤ, c k * fourier k x := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => c k * fourier k x)
  refine ⟨fun x => (F x).re, Complex.continuous_re.comp hFc, ?_, ?_⟩
  · intro k
    simp_rw [hreal]
    exact fourierCoeff_tsum_fourier c hc k
  · let B := 1 + (∑' k : ℤ, ‖c k‖) +
        ∑' k : ℤ, 2 * ‖c k‖ * (2 * Real.pi * |(k : ℝ)|) ^ r
    have hsum0 : 0 ≤ ∑' k : ℤ, ‖c k‖ := tsum_nonneg fun k => norm_nonneg _
    have hw0 : 0 ≤ ∑' k : ℤ, 2 * ‖c k‖ * (2 * Real.pi * |(k : ℝ)|) ^ r :=
      tsum_nonneg fun k => by positivity
    refine ⟨B, by dsimp [B]; linarith, ?_, ?_⟩
    · intro x
      have hbound : |(F x).re| ≤ ∑' k : ℤ, ‖c k‖ := by
        calc |(F x).re| ≤ ‖F x‖ := Complex.abs_re_le_norm _
          _ ≤ ∑' k : ℤ, ‖c k * fourier k x‖ :=
            norm_tsum_le_tsum_norm (by simpa only [norm_mul, norm_fourier_point, mul_one] using hc)
          _ = ∑' k : ℤ, ‖c k‖ := by simp_rw [norm_mul, norm_fourier_point, mul_one]
      exact hbound.trans (by dsimp [B]; linarith)
    · intro x y
      have hs (x : UnitAddCircle) : Summable fun k : ℤ => c k * fourier k x :=
        Summable.of_norm (by simpa only [norm_mul, norm_fourier_point, mul_one] using hc)
      have hn : Summable fun k : ℤ => ‖c k * (fourier k x - fourier k y)‖ := by
        apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ (hc.mul_left 2)
        intro k
        rw [norm_mul]
        have htwo : ‖fourier k x - fourier k y‖ ≤ 2 :=
          (norm_sub_le _ _).trans (by rw [norm_fourier_point, norm_fourier_point]; norm_num)
        nlinarith [norm_nonneg (c k)]
      have hdiff : F x - F y = ∑' k : ℤ, c k * (fourier k x - fourier k y) := by
        dsimp only [F]
        rw [← (hs x).tsum_sub (hs y)]
        exact tsum_congr fun k => by ring
      have hbound : |(F x).re - (F y).re| ≤
          (∑' k : ℤ, 2 * ‖c k‖ * (2 * Real.pi * |(k : ℝ)|) ^ r) * dist x y ^ r := by
        calc
          |(F x).re - (F y).re| = |(F x - F y).re| := by rw [Complex.sub_re]
          _ ≤ ‖F x - F y‖ := Complex.abs_re_le_norm _
          _ ≤ ∑' k : ℤ, ‖c k * (fourier k x - fourier k y)‖ := by
            rw [hdiff]; exact norm_tsum_le_tsum_norm hn
          _ ≤ ∑' k : ℤ, (2 * ‖c k‖ * (2 * Real.pi * |(k : ℝ)|) ^ r) * dist x y ^ r := by
            apply hn.tsum_le_tsum _ (hw.mul_right _)
            intro k
            rw [norm_mul]
            have hh := mul_le_mul_of_nonneg_left
              (norm_fourier_sub_le_holder r hr0 hr1 k x y) (norm_nonneg (c k))
            nlinarith
          _ = (∑' k : ℤ, 2 * ‖c k‖ * (2 * Real.pi * |(k : ℝ)|) ^ r) * dist x y ^ r := tsum_mul_right
      exact hbound.trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (by positivity))

lemma conj_fourierCoeff_real (f : UnitAddCircle → ℝ) (k : ℤ) :
    conj (fourierCoeff (fun x => (f x : ℂ)) k) =
      fourierCoeff (fun x => (f x : ℂ)) (-k) := by
  simp only [fourierCoeff, smul_eq_mul, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, Complex.conj_ofReal, ← fourier_neg]

/-- Dividing real Fourier coefficients by frequency gives a real Hölder primitive whenever
the coefficient power decay has enough room for the desired Hölder exponent. -/
lemma exists_holder_primitive_of_fourier_decay {f : UnitAddCircle → ℝ} {g K r : ℝ}
    (_hK : 0 ≤ K) (hr0 : 0 < r) (hr1 : r ≤ 1) (hgr : g + r < 0)
    (hdecay : ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeff (fun x => (f x : ℂ)) k‖ ≤ K * |(k : ℝ)| ^ g) :
    ∃ G : UnitAddCircle → ℝ, Continuous G ∧
      (∀ k : ℤ, k ≠ 0 → (2 * Real.pi * Complex.I * (k : ℂ)) *
        fourierCoeff (fun x => (G x : ℂ)) k = fourierCoeff (fun x => (f x : ℂ)) k) ∧
      ∃ B : ℝ, 0 < B ∧ (∀ x, |G x| ≤ B) ∧
        ∀ x y, |G x - G y| ≤ B * dist x y ^ r := by
  have hg : g < 0 := by linarith
  let c : ℤ → ℂ := fun k => if k = 0 then 0 else
    fourierCoeff (fun x => (f x : ℂ)) k / (2 * Real.pi * Complex.I * (k : ℂ))
  have hcnorm (k : ℤ) : ‖c k‖ ≤ (K / (2 * Real.pi)) * |(k : ℝ)| ^ (g - 1) := by
    by_cases hk : k = 0
    · simp [c, hk, Real.zero_rpow (show g - 1 ≠ 0 by linarith)]
    · have hkp : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
      simp only [c, hk, ↓reduceIte, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_intCast]
      calc
        ‖fourierCoeff (fun x => (f x : ℂ)) k‖ / (2 * Real.pi * |(k : ℝ)|)
          ≤ (K * |(k : ℝ)| ^ g) / (2 * Real.pi * |(k : ℝ)|) :=
            div_le_div_of_nonneg_right (hdecay k hk) (by positivity)
        _ = K / (2 * Real.pi) * |(k : ℝ)| ^ (g - 1) := by
          rw [Real.rpow_sub_one hkp.ne']
          ring
  have hs : Summable fun k : ℤ => |(k : ℝ)| ^ (g - 1) := by
    convert Real.summable_abs_int_rpow (show 1 < 1 - g by linarith) using 1
    ext k
    congr 1
    ring
  have hc : Summable fun k : ℤ => ‖c k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hcnorm (hs.mul_left _)
  have hwbound (k : ℤ) : 2 * ‖c k‖ * (2 * Real.pi * |(k : ℝ)|) ^ r ≤
      (2 * (K / (2 * Real.pi)) * (2 * Real.pi) ^ r) * |(k : ℝ)| ^ (g - 1 + r) := by
    by_cases hk : k = 0
    · simp [hk, c, Real.zero_rpow (show g - 1 + r ≠ 0 by linarith)]
    · have hkp : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
      calc
        2 * ‖c k‖ * (2 * Real.pi * |(k : ℝ)|) ^ r
          ≤ 2 * ((K / (2 * Real.pi)) * |(k : ℝ)| ^ (g - 1)) *
            (2 * Real.pi * |(k : ℝ)|) ^ r := by gcongr; exact hcnorm k
        _ = (2 * (K / (2 * Real.pi)) * (2 * Real.pi) ^ r) * |(k : ℝ)| ^ (g - 1 + r) := by
          rw [Real.mul_rpow (by positivity) hkp.le, Real.rpow_add hkp]
          ring
  have hsw : Summable fun k : ℤ => |(k : ℝ)| ^ (g - 1 + r) := by
    convert Real.summable_abs_int_rpow (show 1 < -(g - 1 + r) by linarith) using 1
    ext k
    congr 1
    ring
  have hw : Summable fun k : ℤ => 2 * ‖c k‖ * (2 * Real.pi * |(k : ℝ)|) ^ r :=
    Summable.of_nonneg_of_le (fun k => by positivity) hwbound (hsw.mul_left _)
  have hsym (k : ℤ) : conj (c k) = c (-k) := by
    by_cases hk : k = 0
    · simp [c, hk]
    · simp only [c, hk, neg_ne_zero.mpr hk, ↓reduceIte, map_div₀, map_mul,
        Complex.conj_ofReal, Complex.conj_I, conj_fourierCoeff_real, map_ofNat, map_intCast,
        Int.cast_neg]
      congr 1
      ring
  obtain ⟨G, hGc, hGcoeff, B, hB, hGb, hGh⟩ := exists_real_holder_fourierSeries hr0 hr1 c hc hsym hw
  refine ⟨G, hGc, ?_, B, hB, hGb, hGh⟩
  intro k hk
  rw [hGcoeff, show c k = fourierCoeff (fun x => (f x : ℂ)) k /
    (2 * Real.pi * Complex.I * (k : ℂ)) by simp only [c, hk, ↓reduceIte]]
  have hn : (2 * Real.pi * Complex.I * (k : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)) Complex.I_ne_zero
    · exact_mod_cast hk
  exact mul_div_cancel₀ _ hn

lemma exists_primitiveRegularity_of_fourier_decay {f : UnitAddCircle → ℝ}
    (hf : MemLp (fun x => (f x : ℂ)) 2 volume) {g K eta s : ℝ}
    (hK : 0 ≤ K) (hr0 : 0 < 1 - s + eta) (hr1 : 1 - s + eta ≤ 1)
    (hgr : g + (1 - s + eta) < 0)
    (hdecay : ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeff (fun x => (f x : ℂ)) k‖ ≤ K * |(k : ℝ)| ^ g) :
    ∃ B : ℝ, 0 < B ∧ PrimitiveRegularity unitLength eta s B ⟨f, hf⟩ := by
  obtain ⟨G, hGc, hGcoeff, B, hB, hGb, hGh⟩ :=
    exists_holder_primitive_of_fourier_decay hK hr0 hr1 hgr hdecay
  have hmem : MemLp (fun x => (G x : ℂ)) 2 volume :=
    memLp_of_continuous_circle (Complex.continuous_ofReal.comp hGc)
  refine ⟨B, hB, ⟨⟨G, hmem⟩, ?_, ?_⟩⟩
  · exact ⟨hGc, hGb, hGh⟩
  · intro k hk
    change (2 * Real.pi * Complex.I * (k : ℂ) / (1 : ℂ)) *
      fourierCoeff (fun x => (G x : ℂ)) k = fourierCoeff (fun x => (f x : ℂ)) k
    rw [div_one]
    exact hGcoeff k hk

end Internal

/-- The (A1) clause of Assumption 1.1 for proper arc indicators, with the fixed
choice `eta = s/2`. -/
theorem primitiveRegularity_arcIndicator (s : RieszExponent) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (c : UnitAddCircle) :
    ∃ B : ℝ, 0 < B ∧ PrimitiveRegularity unitLength (s.val / 2) s.val B
      ⟨arcIndicator c a, memLp_arcIndicator c a⟩ := by
  apply Internal.exists_primitiveRegularity_of_fourier_decay (g := -1) (K := Real.pi⁻¹)
    (memLp_arcIndicator c a) (by positivity)
    (by linarith [s.2.2]) (by linarith [s.2.1]) (by linarith [s.2.1])
  intro k hk
  rw [fourierCoeff_arcIndicator_centre ha1 c k, norm_mul,
    norm_fourier_unitAddCircle_eq_one, one_mul, fourierCoeff_indicatorArc ha0 ha1 k]
  simp only [hk, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_mul, abs_of_pos Real.pi_pos, Real.rpow_neg_one]
  calc
    |Real.sin (2 * Real.pi * (k : ℝ) * a)| / (Real.pi * |(k : ℝ)|)
      ≤ 1 / (Real.pi * |(k : ℝ)|) :=
        div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
    _ = Real.pi⁻¹ * |(k : ℝ)|⁻¹ := by rw [one_div, mul_inv]

/-- The (A1) clause of Assumption 1.1 for subcritical Riesz power profiles. -/
theorem primitiveRegularity_riesz (s a : RieszExponent) (ha : a.val < s.val / 2) :
    ∃ hf : MemLp (fun x : UnitAddCircle => (rieszRepresentative a x : ℂ)) 2 volume,
      ∃ B : ℝ, 0 < B ∧ PrimitiveRegularity unitLength ((s.val - a.val) / 2) s.val B
        ⟨rieszRepresentative a, hf⟩ := by
  have hf := (circleSobolev_riesz_of_lt s a ha).1
  refine ⟨hf, ?_⟩
  apply Internal.exists_primitiveRegularity_of_fourier_decay (g := a.val - 1)
    (K := rieszConstant a * (2 * Real.pi) ^ (a.val - 1)) hf
    (mul_nonneg (rieszConstant_pos a).le (by positivity))
    (by linarith [s.2.2, a.2.2]) (by linarith [a.2.1, s.2.1]) (by linarith [a.2.1])
  intro k hk
  rw [fourierCoeff_rieszRepresentative]
  simp only [hk, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (mul_pos (rieszConstant_pos a) (by positivity)),
    Real.mul_rpow (by positivity) (abs_nonneg _)]
  exact le_of_eq (by ring)

end Riesz1
