/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalMomentsDefs
public import Riesz1.Auxiliary.LoopArcsBounds
public import Riesz1.Auxiliary.LoopArcsSymm
public import Riesz1.ToMathlib.AbsRpowRadius

/-!
# Uniform microscopic pair bounds and absolute convergence

Ingredients of the local moments part of Lemma 5.8. The kernel constant is
chosen before the particle number. Pair kernels are absolutely integrable on every
bounded interval, for every smooth periodic microscopic test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The first derivative bound, with its constant uniform in the period `N`. -/
theorem loopLocal_deriv_kernel_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (r : ℝ), 0 < r → r ≤ (N : ℝ) / 2 →
      |deriv (loopArcG s N) r| ≤ C * r ^ (-s - 1) := by
  obtain ⟨C, hC, hb⟩ := gradSplit_kernel_deriv_bound s hs hs1
  refine ⟨C, hC, fun N r hr hrR => ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hx0 : 0 < r / N := div_pos hr hN
  have hx1 : r / N ≤ 3 / 4 := by
    rw [div_le_iff₀ hN]
    linarith
  have hbd := hb (r / N) (by rw [abs_of_pos hx0]; exact hx0)
    (by rw [abs_of_pos hx0]; exact hx1) 1 le_rfl (by norm_num)
  rw [iteratedDeriv_one, abs_of_pos hx0, Nat.cast_one] at hbd
  rw [deriv_loopArcG_eq s hs hs1 N hr (by linarith), abs_mul, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hN _), abs_of_pos (inv_pos.mpr hN)]
  have hpow : (r / N) ^ (-s - 1) = r ^ (-s - 1) * (N : ℝ) ^ (s + 1) := by
    rw [show (-s - 1 : ℝ) = -(s + 1) by ring, Real.div_rpow hr.le hN.le,
      Real.rpow_neg hN.le, div_inv_eq_mul]
  have hmul : (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (s + 1)) = 1 := by
    have he : (N : ℝ) ^ (-s) * (N : ℝ) ^ (s + 1) = N := by
      rw [← Real.rpow_add hN]
      norm_num
    calc (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (s + 1))
        = ((N : ℝ) ^ (-s) * (N : ℝ) ^ (s + 1)) * (N : ℝ)⁻¹ := by ring
      _ = 1 := by rw [he, mul_inv_cancel₀ hN.ne']
  calc (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * |deriv (hurwitzKernel s) (r / N)|)
      ≤ (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (C * (r / N) ^ (-s - 1))) := by gcongr
    _ = C * ((N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (s + 1))) * r ^ (-s - 1) := by
      rw [hpow]
      ring
    _ = C * r ^ (-s - 1) := by rw [hmul, mul_one]

/-- On a half period the microscopic pair kernel is bounded by `C Lip(b) |z-u|⁻ˢ`.
The diagonal is included: the pair kernel vanishes there. -/
theorem loopLocal_pair_kernel_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) {b : ℝ → ℝ} {L : NNReal}, LipschitzWith L b →
      ∀ z u : ℝ, |z - u| ≤ (N : ℝ) / 2 →
        |loopArcKernel s N b z u| ≤ C * L * |z - u| ^ (-s) := by
  obtain ⟨C, hC, hb⟩ := loopLocal_deriv_kernel_bound hs hs1
  refine ⟨C, hC, fun N b L hL z u hzu => ?_⟩
  by_cases he : z = u
  · subst u
    rw [loopArcKernel_self, abs_zero]
    positivity
  have hr : 0 < |z - u| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hd : |deriv (loopArcG s N) (z - u)| ≤ C * |z - u| ^ (-s - 1) := by
    rcases le_or_gt 0 (z - u) with hpos | hneg
    · simpa only [abs_of_nonneg hpos] using hb N |z - u| hr hzu
    · have ho := deriv_loopArcG_neg s N (-(z - u))
      rw [neg_neg] at ho
      rw [ho, abs_neg]
      simpa only [abs_of_neg hneg] using hb N |z - u| hr hzu
  have hdiff := hL.norm_sub_le z u
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hdiff
  have hpow : |z - u| * |z - u| ^ (-s - 1) = |z - u| ^ (-s) := by
    rw [Real.rpow_sub_one hr.ne', mul_div_cancel₀ _ hr.ne']
  unfold loopArcKernel
  rw [abs_mul]
  calc |b z - b u| * |deriv (loopArcG s N) (z - u)|
      ≤ ((L : ℝ) * |z - u|) * (C * |z - u| ^ (-s - 1)) :=
        mul_le_mul hdiff hd (abs_nonneg _) (by positivity)
    _ = C * L * |z - u| ^ (-s) := by rw [mul_mul_mul_comm, hpow, mul_comm (L : ℝ) C]

/-- Joint measurability of the pair kernel. -/
theorem measurable_loopLocalKernel {b : ℝ → ℝ} (hb : Continuous b) (s : ℝ) (N : ℕ+) :
    Measurable (fun p : ℝ × ℝ => loopArcKernel s N b p.1 p.2) := by
  exact ((hb.measurable.comp measurable_fst).sub (hb.measurable.comp measurable_snd)).mul
    ((measurable_deriv (loopArcG s N)).comp (measurable_fst.sub measurable_snd))

/-- Periodicity of the pair kernel in the integrated variable. -/
theorem loopLocalKernel_periodic_right {b : ℝ → ℝ} {N : ℕ+}
    (hp : Function.Periodic b (N : ℝ)) (s z : ℝ) :
    Function.Periodic (loopArcKernel s N b z) (N : ℝ) := by
  intro u
  unfold loopArcKernel
  rw [hp u, show z - (u + N) = (z - u) - N by ring,
    (deriv_loopArcG_periodic s N).sub_eq]

/-- All particle/background integrals are absolutely convergent.
This is stated for arbitrary intervals and arbitrary smooth periodic tests. -/
theorem loopLocalKernel_intervalIntegrable {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (N : ℕ+) {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b) (hp : Function.Periodic b (N : ℝ))
    (z a c : ℝ) : IntervalIntegrable (loopArcKernel s N b z) volume a c := by
  have hi : IntervalIntegrable (loopArcKernel s N b z) volume 0 N := by
    have hleft := intervalIntegrable_arc_left s hs hs1 N hb hp z
    have hright := intervalIntegrable_arc_right s hs hs1 N hb hp z
    apply (hleft.add hright).neg.congr
    intro u _
    exact (loopArcKernel_eq_integral_add s N b hb hp z u).symm
  apply (loopLocalKernel_periodic_right hp s z).intervalIntegrable
    (t := 0) (by exact_mod_cast N.ne_zero)
  simpa only [zero_add] using hi

end Riesz1

end
