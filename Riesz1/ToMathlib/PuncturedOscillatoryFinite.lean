/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedOscillatoryIntervals

/-!
# Oscillatory estimates with finitely many singularities

An induction splits the interval at each interior singularity. Singularities outside
the interval are absorbed into the endpoint bounds. The resulting constants are chosen
before the oscillation. This is the finite-partition step.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.PuncturedDerivative

/-- A negative power of the distance to a point outside an interval is controlled by
the powers of the distances to its endpoints. -/
theorem rpow_abs_le_endpoint_sum {a z x y e : ℝ} (he : e ≤ 0)
    (hx : x ∈ Ioo a z) (hy : y ≤ a ∨ z ≤ y) :
    |x - y| ^ e ≤ (x - a) ^ e + (z - x) ^ e := by
  rcases hy with hy | hy
  · have hp : (x - y) ^ e ≤ (x - a) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) (by linarith) he
    rw [abs_of_pos (by linarith [hx.1])]
    exact hp.trans (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith [hx.2]) _))
  · have hp : (y - x) ^ e ≤ (z - x) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by linarith [hx.2]) (by linarith) he
    rw [abs_of_neg (by linarith [hx.2]), neg_sub]
    exact hp.trans (le_add_of_nonneg_left (Real.rpow_nonneg (by linarith [hx.1]) _))

/-- Finitely many interior power singularities give the same oscillatory exponent as
a single endpoint. The constant and frequency threshold may depend on the interval and
the finite singular set. This theorem does not assert uniformity in a varying period. -/
theorem oscillatory_bound_of_finite_deriv_bound {q : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (S : Finset ℝ) {a z C : ℝ} (hC : 0 ≤ C) (haz : a < z)
    (hq : ∀ x ∈ Ioo a z \ (S : Set ℝ), DifferentiableAt ℝ q x)
    (hbound : ∀ x ∈ Ioo a z \ (S : Set ℝ),
      |deriv q x| ≤ C * ((x - a) ^ (-1 - b) + (z - x) ^ (-1 - b) +
        ∑ y ∈ S, |x - y| ^ (-1 - b))) :
    IntervalIntegrable q volume a z ∧
      ∃ K W : ℝ, 0 ≤ K ∧ 1 ≤ W ∧
        ∀ (χ : ℝ → ℂ) (c : ℂ), W ≤ ‖c‖ →
          (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
          ‖∫ t in a..z, (q t : ℂ) * χ t‖ ≤ K * ‖c‖ ^ (b - 1) := by
  classical
  induction S using Finset.induction_on generalizing a z C with
  | empty =>
    exact oscillatory_bound_of_two_endpoint_bounds hb hb1 hC haz
      (by simpa using hq) (by simpa using hbound)
  | @insert y S hyS ih =>
    have hrestrict (u v : ℝ) (hau : a ≤ u) (hvz : v ≤ z) (hy : y ≤ u ∨ v ≤ y) :
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
    by_cases hy : y ∈ Ioo a z
    · have hl := hrestrict a y le_rfl hy.2.le (Or.inr le_rfl)
      have hr := hrestrict y z hy.1.le le_rfl (Or.inl le_rfl)
      obtain ⟨hil, Kl, Wl, hKl, hWl, hbl⟩ := ih (by positivity : 0 ≤ 2 * C) hy.1 hl.1 hl.2
      obtain ⟨hir, Kr, Wr, hKr, hWr, hbr⟩ := ih (by positivity : 0 ≤ 2 * C) hy.2 hr.1 hr.2
      refine ⟨hil.trans hir, Kl + Kr, max Wl Wr, add_nonneg hKl hKr,
        hWl.trans (le_max_left _ _), ?_⟩
      intro χ c hfreq hχ hn
      have hχc : Continuous χ := continuous_iff_continuousAt.mpr fun t => (hχ t).continuousAt
      have hp₁ : IntervalIntegrable (fun t => (q t : ℂ) * χ t) volume a y :=
        (show IntervalIntegrable (fun t => (q t : ℂ)) volume a y from
          ⟨Complex.ofRealCLM.integrable_comp hil.1, Complex.ofRealCLM.integrable_comp hil.2⟩).mul_continuousOn hχc.continuousOn
      have hp₂ : IntervalIntegrable (fun t => (q t : ℂ) * χ t) volume y z :=
        (show IntervalIntegrable (fun t => (q t : ℂ)) volume y z from
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
      have hr := hrestrict a z le_rfl le_rfl hy'
      exact ih (by positivity : 0 ≤ 2 * C) haz hr.1 hr.2

/-- An estimate above a positive frequency threshold extends down to frequency one.
The low frequencies are controlled by the integral of the absolute value of `q`. -/
theorem oscillatory_bound_extend_to_one {q : ℝ → ℝ} {a z g K W : ℝ}
    (haz : a ≤ z) (hi : IntervalIntegrable q volume a z) (hg : g ≤ 0)
    (hK : 0 ≤ K) (hW : 1 ≤ W)
    (hbound : ∀ (χ : ℝ → ℂ) (c : ℂ), W ≤ ‖c‖ →
      (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
      ‖∫ t in a..z, (q t : ℂ) * χ t‖ ≤ K * ‖c‖ ^ g) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (χ : ℝ → ℂ) (c : ℂ), 1 ≤ ‖c‖ →
      (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
      ‖∫ t in a..z, (q t : ℂ) * χ t‖ ≤ K' * ‖c‖ ^ g := by
  let M := ∫ t in a..z, |q t|
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg haz (fun _ _ => abs_nonneg _)
  have hWp : 0 < W := lt_of_lt_of_le zero_lt_one hW
  refine ⟨K + M * W ^ (-g), by positivity, fun χ c hfreq hχ hn => ?_⟩
  by_cases hlarge : W ≤ ‖c‖
  · exact (hbound χ c hlarge hχ hn).trans (by
      nlinarith [Real.rpow_nonneg (norm_nonneg c) g,
        mul_nonneg hM (Real.rpow_nonneg hWp.le (-g))])
  · have hcp : 0 < ‖c‖ := lt_of_lt_of_le zero_lt_one hfreq
    have hp : W ^ g ≤ ‖c‖ ^ g :=
      Real.rpow_le_rpow_of_nonpos hcp (not_le.mp hlarge).le hg
    have hprod : W ^ (-g) * W ^ g = 1 := by
      rw [← Real.rpow_add hWp, neg_add_cancel, Real.rpow_zero]
    have hone : 1 ≤ W ^ (-g) * ‖c‖ ^ g := by
      calc 1 = W ^ (-g) * W ^ g := hprod.symm
        _ ≤ W ^ (-g) * ‖c‖ ^ g := mul_le_mul_of_nonneg_left hp (by positivity)
    have hnorm : ‖∫ t in a..z, (q t : ℂ) * χ t‖ ≤ M := by
      apply intervalIntegral.norm_integral_le_of_norm_le haz
        (ae_of_all volume fun t _ => ?_) hi.abs
      simp only [norm_mul, hn, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact le_rfl
    nlinarith [mul_le_mul_of_nonneg_left hone hM,
      mul_nonneg hK (Real.rpow_nonneg hcp.le g)]

end Riesz1.PuncturedDerivative
