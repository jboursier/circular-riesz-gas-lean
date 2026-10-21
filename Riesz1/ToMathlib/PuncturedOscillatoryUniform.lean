/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedOscillatoryFinite
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniform reference derivative bounds for punctured oscillatory estimates

A bound on a primitive and its second derivative controls the reference derivative
in the endpoint oscillatory estimate. All constants can then be selected before the
function. These lemmas support the uniformity step.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.PuncturedDerivative

/-- The mean value theorem bounds a derivative using a bounded primitive and a bound
on its second derivative, on a fixed interval. -/
theorem abs_deriv_le_of_bounded_primitive {f : ℝ → ℝ} {u v M D x : ℝ}
    (huv : u < v) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Icc u v, DifferentiableAt ℝ f t)
    (hf' : ∀ t ∈ Icc u v, DifferentiableAt ℝ (deriv f) t)
    (hM : ∀ t ∈ Icc u v, |f t| ≤ M)
    (hbound : ∀ t ∈ Icc u v, |deriv (deriv f) t| ≤ D) (hx : x ∈ Icc u v) :
    |deriv f x| ≤ 2 * M / (v - u) + D * (v - u) := by
  obtain ⟨c, hc, hfc⟩ := exists_deriv_eq_slope f huv
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (Ioo_subset_Icc_self ht)).differentiableWithinAt)
  have hc' : c ∈ Icc u v := Ioo_subset_Icc_self hc
  have hdiff := Convex.norm_image_sub_le_of_norm_deriv_le hf'
    (fun t ht => by simpa only [Real.norm_eq_abs] using hbound t ht)
    (convex_Icc u v) hc' hx
  simp only [Real.norm_eq_abs] at hdiff
  have hdist : |x - c| ≤ v - u := abs_le.mpr ⟨by linarith [hx.1, hc.2], by linarith [hx.2, hc.1]⟩
  have hfc' : |deriv f c| ≤ 2 * M / (v - u) := by
    rw [hfc, abs_div, abs_of_pos (sub_pos.mpr huv)]
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr huv).le
    exact (abs_sub _ _).trans (by linarith [hM u (left_mem_Icc.mpr huv.le), hM v (right_mem_Icc.mpr huv.le)])
  have htri : |deriv f x| ≤ |deriv f x - deriv f c| + |deriv f c| := by
    simpa only [sub_add_cancel] using abs_add_le (deriv f x - deriv f c) (deriv f c)
  nlinarith [mul_le_mul_of_nonneg_left hdist hD]

/-- The midpoint reference derivative is uniformly bounded by the primitive bound and
the two-endpoint power bound for its second derivative. -/
theorem abs_deriv_midpoint_le {f : ℝ → ℝ} {a z b C M : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C) (haz : a < z)
    (hf : ∀ x ∈ Ioo a z, DifferentiableAt ℝ f x)
    (hf' : ∀ x ∈ Ioo a z, DifferentiableAt ℝ (deriv f) x)
    (hM : ∀ x ∈ Ioo a z, |f x| ≤ M)
    (hbound : ∀ x ∈ Ioo a z, |deriv (deriv f) x| ≤
      C * ((x - a) ^ (-1 - b) + (z - x) ^ (-1 - b))) :
    |deriv f ((a + z) / 2)| ≤
      2 * M / ((z - a) / 4) +
        (2 * C * ((z - a) / 4) ^ (-1 - b)) * ((z - a) / 4) := by
  let u := (a + z) / 2
  let v := u + (z - a) / 4
  have huv : u < v := by dsimp [u, v]; linarith
  have hsub : Icc u v ⊆ Ioo a z := by
    intro t ht
    dsimp [u, v] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hD : 0 ≤ 2 * C * ((z - a) / 4) ^ (-1 - b) := by positivity
  have hh := abs_deriv_le_of_bounded_primitive huv hD
    (fun t ht => hf t (hsub ht)) (fun t ht => hf' t (hsub ht))
    (fun t ht => hM t (hsub ht)) (fun t ht => ?_) (left_mem_Icc.mpr huv.le)
  · convert hh using 1
    dsimp [v]
    ring
  · have ht₁ : (z - a) / 4 ≤ t - a := by dsimp [u] at ht; linarith [ht.1]
    have ht₂ : (z - a) / 4 ≤ z - t := by dsimp [u, v] at ht; linarith [ht.2]
    have hp₁ := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < (z - a) / 4) ht₁
      (by linarith : -1 - b ≤ 0)
    have hp₂ := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < (z - a) / 4) ht₂
      (by linarith : -1 - b ≤ 0)
    exact (hbound t (hsub ht)).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hp₁ hC,
        mul_le_mul_of_nonneg_left hp₂ hC])


/-- On a fixed interval, the oscillatory estimate is uniform over all primitives with
these supremum and second-derivative bounds. Constants precede the function. -/
theorem uniform_oscillatory_bound_two_endpoints {a z b C M : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C) (hM0 : 0 ≤ M) (haz : a < z) :
    ∃ K W : ℝ, 0 ≤ K ∧ 1 ≤ W ∧ ∀ f : ℝ → ℝ,
      (∀ x ∈ Ioo a z, DifferentiableAt ℝ f x) →
      (∀ x ∈ Ioo a z, DifferentiableAt ℝ (deriv f) x) →
      (∀ x ∈ Ioo a z, |f x| ≤ M) →
      (∀ x ∈ Ioo a z, |deriv (deriv f) x| ≤
        C * ((x - a) ^ (-1 - b) + (z - x) ^ (-1 - b))) →
      IntervalIntegrable (deriv f) volume a z ∧
      ∀ (χ : ℝ → ℂ) (c : ℂ), W ≤ ‖c‖ →
        (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
        ‖∫ t in a..z, ((deriv f t : ℝ) : ℂ) * χ t‖ ≤ K * ‖c‖ ^ (b - 1) := by
  let R := (z - a) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  let Q := 2 * M / ((z - a) / 4) +
    (2 * C * ((z - a) / 4) ^ (-1 - b)) * ((z - a) / 4)
  let K := 6 * Q + 2 * ((2 * C) / b / (1 - b) + 2 * ((2 * C) / b))
  refine ⟨K, max 1 R⁻¹, by dsimp [K, Q]; positivity, le_max_left _ _, ?_⟩
  intro f hf hq hM hbound
  let q := deriv f
  have hleft : ∀ t ∈ Ioc 0 R, a + t ∈ Ioo a z := by
    intro t ht
    constructor <;> dsimp [R] at * <;> linarith [ht.1, ht.2]
  have hright : ∀ t ∈ Ioc 0 R, z - t ∈ Ioo a z := by
    intro t ht
    constructor <;> dsimp [R] at * <;> linarith [ht.1, ht.2]
  have hdl : ∀ t ∈ Ioc 0 R, DifferentiableAt ℝ (fun u => q (a + u)) t := by
    intro t ht
    exact (hq (a + t) (hleft t ht)).comp t (by fun_prop)
  have hdr : ∀ t ∈ Ioc 0 R, DifferentiableAt ℝ (fun u => q (z - u)) t := by
    intro t ht
    exact (hq (z - t) (hright t ht)).comp t (by fun_prop)
  have hbl : ∀ t ∈ Ioc 0 R,
      |deriv (fun u => q (a + u)) t| ≤ (2 * C) * t ^ (-1 - b) := by
    intro t ht
    rw [deriv_comp_const_add]
    have hp : (z - (a + t)) ^ (-1 - b) ≤ t ^ (-1 - b) :=
      Real.rpow_le_rpow_of_nonpos ht.1 (by dsimp [R] at ht; linarith [ht.2]) (by linarith)
    have he := hbound (a + t) (hleft t ht)
    simp only [add_sub_cancel_left] at he
    nlinarith [mul_le_mul_of_nonneg_left hp hC]
  have hbr : ∀ t ∈ Ioc 0 R,
      |deriv (fun u => q (z - u)) t| ≤ (2 * C) * t ^ (-1 - b) := by
    intro t ht
    rw [deriv_comp_const_sub, abs_neg]
    have hp : (z - t - a) ^ (-1 - b) ≤ t ^ (-1 - b) :=
      Real.rpow_le_rpow_of_nonpos ht.1 (by dsimp [R] at ht; linarith [ht.2]) (by linarith)
    have he := hbound (z - t) (hright t ht)
    rw [sub_sub_cancel] at he
    nlinarith [mul_le_mul_of_nonneg_left hp hC]
  have hil : IntervalIntegrable (fun t => q (a + t)) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact integrableOn_of_deriv_rpow_bound hb hb1 (by positivity) hR hdl hbl
  have hir : IntervalIntegrable (fun t => q (z - t)) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact integrableOn_of_deriv_rpow_bound hb hb1 (by positivity) hR hdr hbr
  have hi₁ : IntervalIntegrable q volume a (a + R) := by
    simpa [add_comm, add_left_comm, add_assoc] using hil.comp_add_left (-a)
  have hi₂ : IntervalIntegrable q volume (a + R) z := by
    have heq : z - R = a + R := by dsimp [R]; ring
    simpa [heq] using (hir.comp_sub_left z).symm
  refine ⟨hi₁.trans hi₂, fun χ c hfreq hχ hn => ?_⟩
  let Kl := 3 * |q (a + R)| + (2 * C) / b / (1 - b) + 2 * ((2 * C) / b)
  let Kr := 3 * |q (z - R)| + (2 * C) / b / (1 - b) + 2 * ((2 * C) / b)
  have hmid₁ : a + R = (a + z) / 2 := by dsimp [R]; ring
  have hmid₂ : z - R = (a + z) / 2 := by dsimp [R]; ring
  have href := abs_deriv_midpoint_le hb hC haz hf hq hM hbound
  have hKK : Kl + Kr ≤ K := by
    dsimp [Kl, Kr, K, Q, q]
    rw [hmid₁, hmid₂]
    nlinarith
  have hKK' := mul_le_mul_of_nonneg_right hKK
    (Real.rpow_nonneg (norm_nonneg c) (b - 1))
  have hf : 1 ≤ ‖c‖ := (le_max_left _ _).trans hfreq
  have hcp : 0 < ‖c‖ := lt_of_lt_of_le zero_lt_one hf
  have hfR : ‖c‖⁻¹ ≤ R := (inv_le_comm₀ hcp hR).mpr ((le_max_right _ _).trans hfreq)
  have hl := norm_oscillatory_integral_le_rpow hb hb1 (by positivity : 0 ≤ 2 * C)
    hR hdl hbl hf hfR
    (χ := fun t => χ (a + t)) (c := c)
    (fun t => (hχ (a + t)).comp_const_add a t)
    (fun t => hn (a + t))
  have hr := norm_oscillatory_integral_le_rpow hb hb1 (by positivity : 0 ≤ 2 * C)
    hR hdr hbr (c := -c) (by simpa using hf) (by simpa using hfR)
    (χ := fun t => χ (z - t))
    (fun t => by simpa only [neg_mul] using (hχ (z - t)).comp_const_sub z t)
    (fun t => hn (z - t))
  have hχc : Continuous χ := continuous_iff_continuousAt.mpr fun t => (hχ t).continuousAt
  have hp₁ : IntervalIntegrable (fun t => (q t : ℂ) * χ t) volume a (a + R) :=
    (show IntervalIntegrable (fun t => (q t : ℂ)) volume a (a + R) from
      ⟨Complex.ofRealCLM.integrable_comp hi₁.1, Complex.ofRealCLM.integrable_comp hi₁.2⟩).mul_continuousOn hχc.continuousOn
  have hp₂ : IntervalIntegrable (fun t => (q t : ℂ) * χ t) volume (a + R) z :=
    (show IntervalIntegrable (fun t => (q t : ℂ)) volume (a + R) z from
      ⟨Complex.ofRealCLM.integrable_comp hi₂.1, Complex.ofRealCLM.integrable_comp hi₂.2⟩).mul_continuousOn hχc.continuousOn
  rw [intervalIntegral.integral_comp_add_left (fun u => (q u : ℂ) * χ u) a] at hl
  simp only [add_zero] at hl
  rw [intervalIntegral.integral_comp_sub_left (fun u => (q u : ℂ) * χ u) z] at hr
  simp only [sub_zero, norm_neg] at hr
  rw [show z - R = a + R by dsimp [R]; ring] at hr
  rw [← integral_add_adjacent_intervals hp₁ hp₂]
  apply (norm_add_le _ _).trans
  dsimp [Kl, Kr] at hKK'
  rw [show z - R = a + R by dsimp [R]; ring] at hKK'
  nlinarith [hl, hr, hKK']


/-- For a fixed finite set of real marks, the oscillatory estimate is uniform over all
bounded primitives with the same second-derivative envelope. Constants precede the
function, oscillation and frequency. -/
theorem uniform_oscillatory_bound_finite {b M : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hM0 : 0 ≤ M) (S : Finset ℝ)
    {a z C : ℝ} (hC : 0 ≤ C) (haz : a < z) :
    ∃ K W : ℝ, 0 ≤ K ∧ 1 ≤ W ∧ ∀ f : ℝ → ℝ,
      (∀ x ∈ Ioo a z \ (S : Set ℝ), DifferentiableAt ℝ f x) →
      (∀ x ∈ Ioo a z \ (S : Set ℝ), DifferentiableAt ℝ (deriv f) x) →
      (∀ x ∈ Ioo a z \ (S : Set ℝ), |f x| ≤ M) →
      (∀ x ∈ Ioo a z \ (S : Set ℝ), |deriv (deriv f) x| ≤
        C * ((x - a) ^ (-1 - b) + (z - x) ^ (-1 - b) +
          ∑ y ∈ S, |x - y| ^ (-1 - b))) →
      IntervalIntegrable (deriv f) volume a z ∧
      ∀ (χ : ℝ → ℂ) (c : ℂ), W ≤ ‖c‖ →
        (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
        ‖∫ t in a..z, ((deriv f t : ℝ) : ℂ) * χ t‖ ≤ K * ‖c‖ ^ (b - 1) := by
  classical
  induction S using Finset.induction_on generalizing a z C with
  | empty =>
    simpa using uniform_oscillatory_bound_two_endpoints hb hb1 hC hM0 haz
  | @insert y S hyS ih =>
    have hrestrict {q : ℝ → ℝ}
        (hq : ∀ x ∈ Ioo a z \ (↑(insert y S) : Set ℝ), DifferentiableAt ℝ q x)
        (hbound : ∀ x ∈ Ioo a z \ (↑(insert y S) : Set ℝ),
          |deriv q x| ≤ C * ((x - a) ^ (-1 - b) + (z - x) ^ (-1 - b) +
            ∑ w ∈ insert y S, |x - w| ^ (-1 - b))) (u v : ℝ) (hau : a ≤ u) (hvz : v ≤ z) (hy : y ≤ u ∨ v ≤ y) :
        (∀ x ∈ Ioo u v \ (S : Set ℝ), DifferentiableAt ℝ q x) ∧
        ∀ x ∈ Ioo u v \ (S : Set ℝ),
          |deriv q x| ≤ (2 * C) * ((x - u) ^ (-1 - b) + (v - x) ^ (-1 - b) +
            ∑ w ∈ S, |x - w| ^ (-1 - b)) := by
      have hxorig : ∀ x ∈ Ioo u v \ (S : Set ℝ), x ∈ Ioo a z \ (↑(insert y S) : Set ℝ) := by
        intro x hx
        refine ⟨⟨hau.trans_lt hx.1.1, hx.1.2.trans_le hvz⟩, ?_⟩
        simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
        refine ⟨?_, hx.2⟩
        rcases hy with hy | hy <;> linarith [hx.1.1, hx.1.2]
      refine ⟨fun x hx => hq x (hxorig x hx), ?_⟩
      intro x hx
      have horig := hbound x (hxorig x hx)
      rw [Finset.sum_insert hyS] at horig
      have hl : (x - a) ^ (-1 - b) ≤ (x - u) ^ (-1 - b) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [hx.1.1]) (by linarith) (by linarith)
      have hr : (z - x) ^ (-1 - b) ≤ (v - x) ^ (-1 - b) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [hx.1.2]) (by linarith) (by linarith)
      have hm := rpow_abs_le_endpoint_sum (e := -1 - b) (by linarith) hx.1 hy
      have hs : 0 ≤ ∑ w ∈ S, |x - w| ^ (-1 - b) := Finset.sum_nonneg fun _ _ => by positivity
      nlinarith [mul_le_mul_of_nonneg_left hl hC, mul_le_mul_of_nonneg_left hr hC,
        mul_le_mul_of_nonneg_left hm hC, mul_nonneg hC hs]
    have hsubset (u v : ℝ) (hau : a ≤ u) (hvz : v ≤ z) (hy : y ≤ u ∨ v ≤ y) :
        Ioo u v \ (S : Set ℝ) ⊆ Ioo a z \ (↑(insert y S) : Set ℝ) := by
      intro t ht
      refine ⟨⟨hau.trans_lt ht.1.1, ht.1.2.trans_le hvz⟩, ?_⟩
      simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
      refine ⟨?_, ht.2⟩
      rcases hy with hy | hy <;> linarith [ht.1.1, ht.1.2]
    by_cases hy : y ∈ Ioo a z
    · obtain ⟨Kl, Wl, hKl, hWl, hleft⟩ := ih (by positivity : 0 ≤ 2 * C) hy.1
      obtain ⟨Kr, Wr, hKr, hWr, hright⟩ := ih (by positivity : 0 ≤ 2 * C) hy.2
      refine ⟨Kl + Kr, max Wl Wr, add_nonneg hKl hKr, hWl.trans (le_max_left _ _), ?_⟩
      intro f hf hf' hM hbound
      have hsubL := hsubset a y le_rfl hy.2.le (Or.inr le_rfl)
      have hsubR := hsubset y z hy.1.le le_rfl (Or.inl le_rfl)
      have hl := hrestrict hf' hbound a y le_rfl hy.2.le (Or.inr le_rfl)
      have hr := hrestrict hf' hbound y z hy.1.le le_rfl (Or.inl le_rfl)
      obtain ⟨hil, hbl⟩ := hleft f (fun t ht => hf t (hsubL ht)) hl.1
        (fun t ht => hM t (hsubL ht)) hl.2
      obtain ⟨hir, hbr⟩ := hright f (fun t ht => hf t (hsubR ht)) hr.1
        (fun t ht => hM t (hsubR ht)) hr.2
      refine ⟨hil.trans hir, fun χ c hfreq hχ hn => ?_⟩
      have hχc : Continuous χ := continuous_iff_continuousAt.mpr fun t => (hχ t).continuousAt
      have hp₁ : IntervalIntegrable (fun t => ((deriv f t : ℝ) : ℂ) * χ t) volume a y :=
        (show IntervalIntegrable (fun t => ((deriv f t : ℝ) : ℂ)) volume a y from
          ⟨Complex.ofRealCLM.integrable_comp hil.1, Complex.ofRealCLM.integrable_comp hil.2⟩).mul_continuousOn hχc.continuousOn
      have hp₂ : IntervalIntegrable (fun t => ((deriv f t : ℝ) : ℂ) * χ t) volume y z :=
        (show IntervalIntegrable (fun t => ((deriv f t : ℝ) : ℂ)) volume y z from
          ⟨Complex.ofRealCLM.integrable_comp hir.1, Complex.ofRealCLM.integrable_comp hir.2⟩).mul_continuousOn hχc.continuousOn
      rw [← integral_add_adjacent_intervals hp₁ hp₂]
      exact (norm_add_le _ _).trans (by
        have hlb := hbl χ c ((le_max_left _ _).trans hfreq) hχ hn
        have hrb := hbr χ c ((le_max_right _ _).trans hfreq) hχ hn
        nlinarith)
    · have hy' : y ≤ a ∨ z ≤ y := by
        rcases le_or_gt y a with h | h
        · exact Or.inl h
        · exact Or.inr (not_lt.mp fun hz => hy ⟨h, hz⟩)
      obtain ⟨K, W, hK, hW, hall⟩ := ih (by positivity : 0 ≤ 2 * C) haz
      refine ⟨K, W, hK, hW, fun f hf hf' hM hbound => ?_⟩
      have hsub := hsubset a z le_rfl le_rfl hy'
      have hr := hrestrict hf' hbound a z le_rfl le_rfl hy'
      exact hall f (fun t ht => hf t (hsub ht)) hr.1 (fun t ht => hM t (hsub ht)) hr.2

end Riesz1.PuncturedDerivative
