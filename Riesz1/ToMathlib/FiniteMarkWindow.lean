/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.FiniteMarkMollify

/-!
# Raw convolution windows around finitely many marks

The locally integrable first transport derivative can be integrated across its
marks. These estimates support the second derivative in Lemma 5.1.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Translating an integration window translates its integrand. -/
theorem integral_window_translate (f : ℝ → ℝ) (x r a : ℝ) :
    (∫ y in Ioo (x - r) (x + r), f (y - a)) =
      ∫ y in Ioo (x - a - r) (x - a + r), f y := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo]
  by_cases hr : 0 ≤ r
  · rw [← intervalIntegral.integral_of_le (by linarith : x - r ≤ x + r),
      ← intervalIntegral.integral_of_le (by linarith : x - a - r ≤ x - a + r),
      intervalIntegral.integral_comp_sub_right]
    congr 1 <;> ring
  · have h1 : Ioc (x - r) (x + r) = ∅ := Ioc_eq_empty_of_le (by linarith)
    have h2 : Ioc (x - a - r) (x - a + r) = ∅ := Ioc_eq_empty_of_le (by linarith)
    simp only [h1, h2, setIntegral_empty]

/-- The integral of one circular singularity over any window has the
uniform `h^(1-b)` bound. Its constant precedes the period and the mark. -/
theorem integral_window_circle_dist_rpow {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L → ∀ a h : ℝ, 0 < h → h ≤ 1 →
      ∀ x : ℝ, (∫ y in Ioo (x - h / 2) (x + h / 2),
        dist (y : AddCircle L) (a : AddCircle L) ^ (-b)) ≤ A * h ^ (1 - b) := by
  let A := (2 : ℝ) ^ b + 8 * (3 / 2 : ℝ) ^ (1 - b) / (1 - b)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, fun L hL a h hh hh1 x => ?_⟩
  have hLp : 0 < L := by linarith
  have : Fact (0 < L) := ⟨hLp⟩
  let F := fun y : ℝ => dist (y : AddCircle L) 0 ^ (-b)
  have hi : LocallyIntegrable F volume := locallyIntegrable_circle_dist_rpow hLp (by linarith)
  have hp : Function.Periodic F L := by intro y; simp only [F, AddCircle.coe_add_period]
  have hn (y : ℝ) : 0 ≤ F y := by dsimp [F]; positivity
  have he (y : ℝ) : dist (y : AddCircle L) (a : AddCircle L) ^ (-b) = F (y - a) := by
    simp only [F, AddCircle.coe_sub, dist_eq_norm, sub_zero]
  simp_rw [he]
  rw [integral_window_translate]
  let z := x - a
  change (∫ y in Ioo (z - h / 2) (z + h / 2), F y) ≤ _
  have hf : ∀ᵐ y : ℝ, circDist L y ≠ 0 → |F y| ≤ circDist L y ^ (-b) := by
    exact ae_of_all _ fun y _ => by
      rw [← dist_coe_zero_eq_circDist, abs_of_nonneg (hn y)]
  by_cases hz : h ≤ circDist L z
  · have hw := window_abs_le_far_gen (circDist_le_add_abs hLp) hi hb hh hf hz
    simp_rw [abs_of_nonneg (hn _)] at hw
    have hr : (circDist L z / 2) ^ (-b) ≤ (h / 2) ^ (-b) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have hid : h * (h / 2) ^ (-b) = 2 ^ b * h ^ (1 - b) := by
      rw [div_two_rpow_neg hh.le, ← inv_mul_rpow_one_sub hh]
      field_simp
    refine hw.trans ((mul_le_mul_of_nonneg_left hr hh.le).trans ?_)
    rw [hid]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [A]
    exact le_add_of_nonneg_right (by positivity)
  · let t := z - L * (round (z / L) : ℝ)
    have ht : |t| ≤ h := (show |t| = circDist L z from rfl).trans_le (le_of_not_ge hz)
    have hshift : (∫ y in Ioo (z - h / 2) (z + h / 2), F y) =
        ∫ y in Ioo (t - h / 2) (t + h / 2), F y := by
      have heq (y : ℝ) : F (y - L * (round (z / L) : ℝ)) = F y := by
        simpa only [mul_comm L] using hp.sub_int_mul_eq (round (z / L)) (x := y)
      conv_lhs => arg 2; ext y; rw [← heq y]
      exact integral_window_translate F z (h / 2) (L * (round (z / L) : ℝ))
    rw [hshift]
    have hfb : ∀ᵐ y : ℝ, y ∈ Icc (-(L / 2)) (L / 2) →
        |F y - 0| ≤ |y| ^ (-b) := by
      exact ae_of_all _ fun y hy => by
        rw [sub_zero, abs_of_nonneg (hn y)]
        dsimp [F]
        rw [dist_coe_zero_eq_circDist, circDist_eq_abs hLp (abs_le.mpr hy)]
    have hBi : IntegrableOn (fun y : ℝ => |y| ^ (-b)) (Icc (-(L / 2)) (L / 2)) :=
      integrableOn_abs_rpow (by linarith) (by linarith)
    have hw : (∫ y in Ioo (t - h / 2) (t + h / 2), F y) ≤
        8 * ((3 / 2 * h) ^ (1 - b) / (1 - b)) := by
      by_cases h3 : 3 * h ≤ L
      · have hw := integral_window_sub_le_of_le (B := fun r : ℝ => r ^ (-b)) hh h3 ht hi hfb
          (ae_of_all _ fun y _ => Real.rpow_nonneg (abs_nonneg y) (-b)) hBi
        simp only [sub_zero, abs_of_nonneg (hn _)] at hw
        rw [integral_rpow_neg_zero_to hb1] at hw
        linarith [show 0 ≤ (3 / 2 * h) ^ (1 - b) / (1 - b) by positivity]
      · have hw := integral_window_sub_le_of_lt (B := fun r : ℝ => r ^ (-b)) hp hLp (by linarith : h ≤ L) ht hi hfb hBi
        simp only [sub_zero, abs_of_nonneg (hn _)] at hw
        rw [integral_rpow_neg_zero_to hb1] at hw
        have hr := Real.rpow_le_rpow (by linarith : 0 ≤ L / 2)
          (by linarith : L / 2 ≤ 3 / 2 * h) (by linarith : 0 ≤ 1 - b)
        exact hw.trans (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hr (by linarith)) (by norm_num))
    refine hw.trans ?_
    rw [Real.mul_rpow (by norm_num : 0 ≤ (3 / 2 : ℝ)) hh.le]
    dsimp [A]
    have hpow : 0 ≤ h ^ (1 - b) := by positivity
    have heq : 8 * ((3 / 2 : ℝ) ^ (1 - b) * h ^ (1 - b) / (1 - b)) =
        (8 * (3 / 2 : ℝ) ^ (1 - b) / (1 - b)) * h ^ (1 - b) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hpow

/-- A finite singular envelope has a uniform raw-window estimate. -/
theorem integral_window_finiteMark_bound {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L →
      ∀ {ι : Type*} [Fintype ι] (marks : ι → ℝ) (C : ℝ), 0 ≤ C →
      ∀ f : ℝ → ℝ, LocallyIntegrable f volume →
      (∀ᵐ y : ℝ, |f y| ≤ C * (1 + ∑ j, dist (y : AddCircle L) (marks j : AddCircle L) ^ (-b))) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
        (∫ y in Ioo (x - h / 2) (x + h / 2), |f y|) ≤
          C * (1 + (Fintype.card ι : ℝ) * A) * h ^ (1 - b) := by
  obtain ⟨A, hA, hsingle⟩ := integral_window_circle_dist_rpow hb hb1
  refine ⟨A, hA, fun L hL ι _ marks C hC f hf henv h hh hh1 x => ?_⟩
  have hLp : 0 < L := by linarith
  have : Fact (0 < L) := ⟨hLp⟩
  let W := Ioo (x - h / 2) (x + h / 2)
  let G := fun j (y : ℝ) => dist (y : AddCircle L) (marks j : AddCircle L) ^ (-b)
  have hi (j : ι) : IntegrableOn (G j) W := by
    have ht := locallyIntegrable_translate_sub
      (locallyIntegrable_circle_dist_rpow hLp (show -1 < -b by linarith)) (marks j)
    have ht' : LocallyIntegrable (G j) volume := by
      simpa only [G, AddCircle.coe_sub, dist_eq_norm, sub_zero] using ht
    exact (ht'.integrableOn_isCompact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hsum : IntegrableOn (fun y => ∑ j, G j y) W := integrable_finsetSum _ (fun j _ => hi j)
  have hmajor : (∫ y in W, |f y|) ≤ ∫ y in W, C * (1 + ∑ j, G j y) :=
    setIntegral_mono_ae_restrict
      (((hf.integrableOn_isCompact isCompact_Icc).mono_set Ioo_subset_Icc_self).abs)
      ((integrableOn_const (by dsimp [W]; simp)).add hsum |>.const_mul C)
      (ae_restrict_of_ae henv)
  have hvol : (∫ _y : ℝ in W, (1 : ℝ)) = h := by
    dsimp [W]
    rw [setIntegral_const, measureReal_def, Real.volume_Ioo, smul_eq_mul,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [integral_const_mul, integral_add (integrableOn_const (by dsimp [W]; simp)) hsum,
    hvol, integral_finsetSum _ (fun j _ => hi j)] at hmajor
  have hterms := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => hsingle L hL (marks j) h hh hh1 x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hterms
  have hhpow : h ≤ h ^ (1 - b) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hh hh1 (show 1 - b ≤ 1 by linarith)
  refine hmajor.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hterms hC,
    mul_le_mul_of_nonneg_left hhpow hC]

end Riesz1
