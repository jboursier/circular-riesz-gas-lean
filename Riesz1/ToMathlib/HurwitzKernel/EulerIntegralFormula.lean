/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.EulerIntegralLimit

/-!
# The integral formulas for the Hurwitz zeta function at real `x > 0`

Lemma 2.1, integral formula in equation (2.11) (second line), for
`Re z > 0` and `z ≠ 1`:
`ζ(z, x) = x^{1-z}/(z-1) + x^{-z}/2 - z ∫_0^∞ B_1(t) (t + x)^{-1-z} dt`.

The file also proves the second-order form of the `B_1` integral, which is absolutely convergent
for `Re z > -1` and is used to continue the formula analytically in `Riesz1.EulerIntegralAnalytic`:
`∫_0^∞ B_1(t) (t+x)^{-1-z} dt = -x^{-1-z}/12 + (1+z) ∫_0^∞ B_2(t) (t+x)^{-2-z} dt`.
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral

namespace Riesz1

/-- The derivative of `t ↦ (t + x)^w` on `[0, ∞)` for `x > 0`. -/
lemma hasDerivAt_cpow_add_real {x : ℝ} (hx : 0 < x) (w : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => ((t : ℂ) + x) ^ w) (w * ((t : ℂ) + x) ^ (w - 1)) t := by
  have hs : ((t : ℂ) + x) ∈ Complex.slitPlane := by
    have h : (((t + x : ℝ)) : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.mpr (by linarith)
    push_cast at h
    exact h
  have he : HasDerivAt (fun u : ℂ => (u + x) ^ w) (w * ((t : ℂ) + x) ^ (w - 1) * 1) (t : ℂ) :=
    ((hasDerivAt_id (t : ℂ)).add_const (x : ℂ)).cpow_const hs
  simpa using he.comp_ofReal

/-- Continuity of `t ↦ (t + x)^w` on `[0, ∞)`. -/
lemma continuousAt_cpow_add_real {x : ℝ} (hx : 0 < x) (w : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun t : ℝ => ((t : ℂ) + x) ^ w) t :=
  (hasDerivAt_cpow_add_real hx w ht).continuousAt

/-- The integral of `(t + x)^w` over `[0, M]`, for `w + 1 ≠ 0`. -/
lemma integral_cpow_add_real {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : w + 1 ≠ 0) (M : ℕ) :
    ∫ t in (0 : ℝ)..(M : ℝ), ((t : ℂ) + x) ^ w =
      ((((M : ℝ) : ℂ) + x) ^ (w + 1) - ((0 : ℝ) + x : ℂ) ^ (w + 1)) / (w + 1) := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hd : ∀ t ∈ uIcc (0 : ℝ) (M : ℝ),
      HasDerivAt (fun t : ℝ => ((t : ℂ) + x) ^ (w + 1) / (w + 1)) (((t : ℂ) + x) ^ w) t := by
    intro t ht
    rw [uIcc_of_le hM] at ht
    have h := (hasDerivAt_cpow_add_real hx (w + 1) ht.1).div_const (w + 1)
    convert h using 1
    rw [show w + 1 - 1 = w by ring]
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ => ((t : ℂ) + x) ^ w) volume 0 (M : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hM] at ht
    exact (continuousAt_cpow_add_real hx w ht.1).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  ring

/-- The trapezoid identity for `∫_0^M F + ∫_0^M B_1 F'`, in the form `∑_{n ≤ M} F(n)`. -/
lemma sum_range_succ_eq_trapezoid {F F' : ℝ → ℂ}
    (hF : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (F' t) t) (hF'c : ContinuousOn F' (Ici 0)) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), F n =
      (∫ t in (0 : ℝ)..(M : ℝ), F t) + (∫ t in (0 : ℝ)..(M : ℝ), (sawtoothB1 t : ℂ) * F' t) +
        (F 0 + F M) / 2 := by
  have h := sum_trapezoid_eq hF hF'c M
  have hS : ∑ n ∈ Finset.range (M + 1), F n = ∑ n ∈ Finset.range M, F n + F M :=
    Finset.sum_range_succ (fun n : ℕ => F n) M
  have hS2 : ∑ n ∈ Finset.range (M + 1), F n = ∑ n ∈ Finset.range M, F ((n : ℝ) + 1) + F 0 := by
    rw [Finset.sum_range_succ']
    simp
  have hT : ∑ n ∈ Finset.range M, (F n + F ((n : ℝ) + 1)) / 2 =
      ((∑ n ∈ Finset.range M, F n) + ∑ n ∈ Finset.range M, F ((n : ℝ) + 1)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  linear_combination -h - hT + (1 / 2 : ℂ) * hS + (1 / 2 : ℂ) * hS2

/-- The integrable power `(t + x)^w` on `(0, ∞)` for `x > 0` and `Re w < 0`, at the level of
the limit `M ↦ (M + x)^w`. -/
lemma tendsto_cpow_natCast_add {x : ℝ} (hx : 0 ≤ x) {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun M : ℕ => ((M : ℂ) + x) ^ w) atTop (𝓝 0) := by
  have h1 := tendsto_cpow_add_sub (w := w) (by linarith) (h := x) hx
  have h2 := tendsto_natCast_cpow_zero w hw
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr (fun M => ?_)
  push_cast
  ring

/-- The second-order form: the `B_1` integral against `(t + x)^{-1-z}` for `Re z > 0`. -/
theorem integral_sawtoothB1_eq_B2 {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (sawtoothB1 t : ℂ) * ((t : ℂ) + x) ^ (-(1 + z)) =
      -(((x : ℂ)) ^ (-(1 + z))) / 12 +
        (1 + z) * ∫ t in Ioi (0 : ℝ), (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + z)) := by
  set G : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (-(1 + z)) with hGdef
  set G' : ℝ → ℂ := fun t => (-(1 + z)) * ((t : ℂ) + x) ^ (-(1 + z) - 1) with hG'def
  have hG : ∀ t : ℝ, 0 ≤ t → HasDerivAt G (G' t) t := fun t ht =>
    hasDerivAt_cpow_add_real hx (-(1 + z)) ht
  have hG'c : ContinuousOn G' (Ici 0) := fun t ht =>
    ((continuousAt_cpow_add_real hx (-(1 + z) - 1) ht).const_mul _).continuousWithinAt
  have hsum := sum_sawtoothB1_mul_eq hG hG'c
  -- integrability on `(0, ∞)`
  have hint1 : IntegrableOn (fun t : ℝ => (sawtoothB1 t : ℂ) * G t) (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 + z))) (Ioi 0) :=
      integrableOn_Ioi_add_cpow hx (by simp; linarith)
    refine Integrable.bdd_mul (c := 1 / 2) hg ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp sawtoothB1_measurable).aestronglyMeasurable
    · exact ae_of_all _ (fun t => by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sawtoothB1_le t)
  have hint2 : IntegrableOn (fun t : ℝ => (sawtoothB2 t : ℂ) * G' t) (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(2 + z))) (Ioi 0) :=
      integrableOn_Ioi_add_cpow hx (by simp; linarith)
    have hb : IntegrableOn (fun t : ℝ => (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + z))) (Ioi 0) := by
      refine Integrable.bdd_mul (c := 1 / 12) hg ?_ ?_
      · exact (Complex.continuous_ofReal.measurable.comp sawtoothB2_measurable).aestronglyMeasurable
      · exact ae_of_all _ (fun t => by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_sawtoothB2_le t)
    refine IntegrableOn.congr_fun (f := fun t : ℝ => -(1 + z) * ((sawtoothB2 t : ℂ) *
      ((t : ℂ) + x) ^ (-(2 + z)))) (hb.const_mul (-(1 + z))) (fun t _ => ?_) measurableSet_Ioi
    simp only [hG'def]
    rw [show -(2 + z) = -(1 + z) - 1 by ring]
    ring
  -- the three limits
  have hL1 : Tendsto (fun M : ℕ => ∫ t in (0 : ℝ)..(M : ℝ), (sawtoothB1 t : ℂ) * G t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), (sawtoothB1 t : ℂ) * G t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint1 tendsto_natCast_atTop_atTop
  have hL2 : Tendsto (fun M : ℕ => G M) atTop (𝓝 0) := by
    have := tendsto_cpow_natCast_add hx.le (w := -(1 + z)) (by simp; linarith)
    refine this.congr (fun M => ?_)
    simp [hGdef]
  have hL3 : Tendsto (fun M : ℕ => ∫ t in (0 : ℝ)..(M : ℝ), (sawtoothB2 t : ℂ) * G' t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), (sawtoothB2 t : ℂ) * G' t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint2 tendsto_natCast_atTop_atTop
  have hlim := (((hL2.sub_const (G 0)).div_const 12).sub hL3)
  have hlim' : Tendsto (fun M : ℕ => ∫ t in (0 : ℝ)..(M : ℝ), (sawtoothB1 t : ℂ) * G t) atTop
      (𝓝 (((0 : ℂ) - G 0) / 12 - ∫ t in Ioi (0 : ℝ), (sawtoothB2 t : ℂ) * G' t)) := by
    refine hlim.congr (fun M => ?_)
    exact (hsum M).symm
  have hval := tendsto_nhds_unique hL1 hlim'
  rw [hval]
  have hG0 : G 0 = ((x : ℂ)) ^ (-(1 + z)) := by
    simp [hGdef]
  have hB2 : ∫ t in Ioi (0 : ℝ), (sawtoothB2 t : ℂ) * G' t =
      -(1 + z) * ∫ t in Ioi (0 : ℝ), (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + z)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [hG'def]
    rw [show -(2 + z) = -(1 + z) - 1 by ring]
    ring
  rw [hG0, hB2]
  ring


/-- Euler's integral formula for `ζ(z, x)` with the sawtooth `B_1`, for `Re z > 0` and `z ≠ 1`
(equation (2.11), second line). -/
theorem hurwitzZetaPos_eq_integral {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    hurwitzZetaPos z x = (x : ℂ) ^ (1 - z) / (z - 1) + (x : ℂ) ^ (-z) / 2 -
      z * ∫ t in Ioi (0 : ℝ), ((sawtoothB1 t : ℝ) : ℂ) / ((t : ℂ) + x) ^ (1 + z) := by
  set F : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (-z) with hFdef
  set F' : ℝ → ℂ := fun t => (-z) * ((t : ℂ) + x) ^ (-z - 1) with hF'def
  have hF : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (F' t) t := fun t ht =>
    hasDerivAt_cpow_add_real hx (-z) ht
  have hF'c : ContinuousOn F' (Ici 0) := fun t ht =>
    ((continuousAt_cpow_add_real hx (-z - 1) ht).const_mul _).continuousWithinAt
  have hw : -z + 1 ≠ 0 := by
    intro h
    apply hz1
    linear_combination -h
  -- integrability of the sawtooth against `F'` on `(0, ∞)`
  have hint : IntegrableOn (fun t : ℝ => (sawtoothB1 t : ℂ) * F' t) (Ioi 0) := by
    have hg : IntegrableOn (fun t : ℝ => ((t : ℂ) + x) ^ (-z - 1)) (Ioi 0) :=
      integrableOn_Ioi_add_cpow hx (by simp; linarith)
    have hb : IntegrableOn (fun t : ℝ => (sawtoothB1 t : ℂ) * ((t : ℂ) + x) ^ (-z - 1)) (Ioi 0) := by
      refine Integrable.bdd_mul (c := 1 / 2) hg ?_ ?_
      · exact (Complex.continuous_ofReal.measurable.comp sawtoothB1_measurable).aestronglyMeasurable
      · exact ae_of_all _ (fun t => by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_sawtoothB1_le t)
    refine IntegrableOn.congr_fun (f := fun t : ℝ => (-z) *
      ((sawtoothB1 t : ℂ) * ((t : ℂ) + x) ^ (-z - 1))) (hb.const_mul (-z))
      (fun t _ => ?_) measurableSet_Ioi
    simp only [hF'def]
    ring
  -- the integral of `B_1 F'` is `-z` times the integral in the statement
  have hI : ∫ t in Ioi (0 : ℝ), (sawtoothB1 t : ℂ) * F' t =
      -z * ∫ t in Ioi (0 : ℝ), ((sawtoothB1 t : ℝ) : ℂ) / ((t : ℂ) + x) ^ (1 + z) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [hF'def]
    rw [show -z - 1 = -(1 + z) by ring, Complex.cpow_neg, div_eq_mul_inv]
    ring
  have hI_tend : Tendsto (fun M : ℕ => ∫ t in (0 : ℝ)..(M : ℝ), (sawtoothB1 t : ℂ) * F' t)
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), (sawtoothB1 t : ℂ) * F' t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop
  -- the shifted powers
  have hA : Tendsto (fun M : ℕ => (((M : ℝ) : ℂ) + x) ^ (1 - z) - (M : ℂ) ^ (1 - z)) atTop
      (𝓝 0) := by
    have h := tendsto_cpow_add_sub (w := 1 - z) (by simp; linarith) hx.le
    refine h.congr (fun M => ?_)
    push_cast
    rfl
  have hB : Tendsto (fun M : ℕ => (((M : ℝ) : ℂ) + x) ^ (-z)) atTop (𝓝 0) :=
    tendsto_cpow_natCast_add hx.le (by simp; linarith)
  -- the regularized partial sums as a sum of the trapezoid identity
  have key : ∀ M : ℕ, (∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-z)) -
      (M : ℂ) ^ (1 - z) / (1 - z) =
      ((((M : ℝ) : ℂ) + x) ^ (1 - z) - (M : ℂ) ^ (1 - z)) / (1 - z) +
        (∫ t in (0 : ℝ)..(M : ℝ), (sawtoothB1 t : ℂ) * F' t) +
        ((x : ℂ) ^ (-z) + (((M : ℝ) : ℂ) + x) ^ (-z)) / 2 - (x : ℂ) ^ (1 - z) / (1 - z) := by
    intro M
    have hs := sum_range_succ_eq_trapezoid hF hF'c M
    have hIF : ∫ t in (0 : ℝ)..(M : ℝ), F t =
        ((((M : ℝ) : ℂ) + x) ^ (1 - z) - (x : ℂ) ^ (1 - z)) / (1 - z) := by
      have h := integral_cpow_add_real hx hw M
      rw [show -z + 1 = 1 - z by ring] at h
      simp only [hFdef]
      rw [h]
      simp
    have hF0 : F 0 = (x : ℂ) ^ (-z) := by simp [hFdef]
    have hFM : F M = (((M : ℝ) : ℂ) + x) ^ (-z) := rfl
    rw [hIF, hF0, hFM] at hs
    simp only [hFdef, Complex.ofReal_natCast] at hs
    simp only [Complex.ofReal_natCast]
    linear_combination hs
  have hC0 : Tendsto (fun _ : ℕ => (x : ℂ) ^ (-z)) atTop (𝓝 ((x : ℂ) ^ (-z))) :=
    tendsto_const_nhds
  have hC : Tendsto (fun M : ℕ => ((x : ℂ) ^ (-z) + (((M : ℝ) : ℂ) + x) ^ (-z)) / 2) atTop
      (𝓝 (((x : ℂ) ^ (-z) + 0) / 2)) :=
    (hC0.add hB).div_const 2
  have h1 := (hA.div_const (1 - z)).add hI_tend
  have h2 := h1.add hC
  have h3 := h2.sub_const ((x : ℂ) ^ (1 - z) / (1 - z))
  have hR := h3.congr (fun M => (key M).symm)
  have heq := tendsto_nhds_unique (tendsto_hurwitzZetaPos hx hz hz1) hR
  rw [heq, hI]
  have hsign : z - 1 = -(1 - z) := by ring
  rw [hsign, div_neg]
  ring

end Riesz1

end
