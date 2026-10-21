/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedDerivative
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Integrable derivatives across isolated singularities

A punctured bound on the derivative of `q` with exponent `-1-b`, `0<b<1`, gives
integrability on both sides of the puncture. A continuous function with a locally
integrable derivative and only countably many possible points of nondifferentiability
is absolutely continuous on every compact interval. These are gluing tools for the admissibility
regularity lemma.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz1.PuncturedDerivative

/-- The one-sided power estimate gives integrability on a whole interval around a puncture. -/
theorem intervalIntegrable_of_punctured_deriv_bound {q : ℝ → ℝ} {a b C R : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C) (hR : 0 < R)
    (hd : ∀ t : ℝ, 0 < |t - a| → |t - a| ≤ R → DifferentiableAt ℝ q t)
    (hbound : ∀ t : ℝ, 0 < |t - a| → |t - a| ≤ R →
      |deriv q t| ≤ C * |t - a| ^ (-1 - b)) :
    IntervalIntegrable q volume (a - R) (a + R) := by
  have hright : IntervalIntegrable (fun t : ℝ => q (a + t)) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    apply integrableOn_of_deriv_rpow_bound hb hb1 hC hR
    · intro t ht
      have hdq := hd (a + t) (by simpa [abs_of_pos ht.1] using ht.1) (by simpa [abs_of_pos ht.1] using ht.2)
      exact hdq.comp t (by fun_prop)
    · intro t ht
      have hdq := hd (a + t) (by simpa [abs_of_pos ht.1] using ht.1) (by simpa [abs_of_pos ht.1] using ht.2)
      have he : deriv (fun t : ℝ => q (a + t)) t = deriv q (a + t) := by
        exact deriv_comp_const_add q a t
      rw [he]
      simpa [abs_of_pos ht.1] using
        hbound (a + t) (by simpa [abs_of_pos ht.1] using ht.1) (by simpa [abs_of_pos ht.1] using ht.2)
  have hleft : IntervalIntegrable (fun t : ℝ => q (a - t)) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    apply integrableOn_of_deriv_rpow_bound hb hb1 hC hR
    · intro t ht
      have hdq := hd (a - t) (by simpa [abs_of_pos ht.1] using ht.1) (by simpa [abs_of_pos ht.1] using ht.2)
      exact hdq.comp t (by fun_prop)
    · intro t ht
      have hdq := hd (a - t) (by simpa [abs_of_pos ht.1] using ht.1) (by simpa [abs_of_pos ht.1] using ht.2)
      have he : deriv (fun t : ℝ => q (a - t)) t = -(deriv q (a - t)) := by
        exact deriv_comp_const_sub q a t
      rw [he, abs_neg]
      simpa [abs_of_pos ht.1] using
        hbound (a - t) (by simpa [abs_of_pos ht.1] using ht.1) (by simpa [abs_of_pos ht.1] using ht.2)
  have hr : IntervalIntegrable q volume a (a + R) := by
    simpa [add_comm] using (IntervalIntegrable.comp_add_right_iff (c := a)).mp
      (show IntervalIntegrable (fun t : ℝ => q (t + a)) volume 0 R by
        simpa [add_comm] using hright)
  have hl : IntervalIntegrable q volume (a - R) a := by
    simpa using (hleft.comp_sub_left a).symm
  exact hl.trans hr

/-- Local punctured power bounds give local integrability, including at every puncture. -/
theorem locallyIntegrable_of_punctured_deriv_bound {q : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hb1 : b < 1)
    (hlocal : ∀ a : ℝ, ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      (∀ t : ℝ, 0 < |t - a| → |t - a| ≤ R → DifferentiableAt ℝ q t) ∧
      ∀ t : ℝ, 0 < |t - a| → |t - a| ≤ R →
        |deriv q t| ≤ C * |t - a| ^ (-1 - b)) : LocallyIntegrable q volume := by
  intro a
  obtain ⟨R, C, hR, hC, hd, hbound⟩ := hlocal a
  have hi := intervalIntegrable_of_punctured_deriv_bound hb hb1 hC hR hd hbound
  refine ⟨Icc (a - R) (a + R), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : a - R ≤ a + R)).mp hi

/-- Reconstruction by the integral of the derivative rules out any singular continuous
part when nondifferentiability is confined to a countable set. -/
theorem absolutelyContinuousOnInterval_of_countable_exceptional {f : ℝ → ℝ}
    (hc : Continuous f) {S : Set ℝ} (hS : S.Countable)
    (hd : ∀ x : ℝ, x ∉ S → DifferentiableAt ℝ f x)
    (hi : LocallyIntegrable (deriv f) volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b := by
  have hab : IntervalIntegrable (deriv f) volume a b := by
    exact (intervalIntegrable_iff' (by finiteness)).mpr
      (hi.integrableOn_isCompact isCompact_uIcc)
  have hAC := hab.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc (a := a) (b := b))
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.add hAC).congr
  intro x _hx
  have hix : IntervalIntegrable (deriv f) volume a x := by
    exact (intervalIntegrable_iff' (by finiteness)).mpr
      (hi.integrableOn_isCompact isCompact_uIcc)
  have he := integral_eq_of_hasDerivAt_off_countable f (deriv f) hS hc.continuousOn
    (fun t ht => (hd t ht.2).hasDerivAt) hix
  change f a + (∫ t in a..x, deriv f t) = f x
  rw [he]
  ring

end Riesz1.PuncturedDerivative
