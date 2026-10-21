/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsPair

/-!
# Scaled derivative bounds for the microscopic kernel

The microscopic kernel `g_N(r) = N^{-s} g(r / N)` satisfies, on `0 < r < N`,
`g_N'(r) = N^{-s-1} g'(r / N)`. Combined with the derivative bound
`|g'(x)| ≤ C |x|^{-s-1}` of `gradient_splitting_kernel` (proved in
`Riesz1/Auxiliary/GradientSplittingKernel.lean`), this gives the scale-invariant bound
`|g_N'(r)| ≤ C r^{-s-1}` on `0 < r ≤ N/2`, used for the integrability of the cutoff `Q`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The derivative of the microscopic kernel on `(0, N)`, by the chain rule. -/
theorem deriv_loopArcG_eq (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) {r : ℝ}
    (hr : 0 < r) (hrN : r < (N : ℝ)) :
    deriv (loopArcG s N) r = (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * deriv (hurwitzKernel s) (r / N)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hx : ((r / N : ℝ) : UnitAddCircle) ≠ 0 := by
    apply gradSplit_coe_ne_zero
    · rw [abs_of_pos (div_pos hr hN)]
      exact div_pos hr hN
    · rw [abs_of_pos (div_pos hr hN)]
      exact (div_lt_one hN).mpr hrN
  have hg : HasDerivAt (hurwitzKernel s) (iteratedDeriv 1 (hurwitzKernel s) (r / N)) (r / N) := by
    have h := gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 0 hx
    simpa only [iteratedDeriv_zero] using h
  have hlin : HasDerivAt (fun x : ℝ => x / (N : ℝ)) ((N : ℝ)⁻¹) r := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id r).mul_const ((N : ℝ)⁻¹)
  have hcomp := hg.comp r hlin
  have hfull : HasDerivAt (loopArcG s N)
      ((N : ℝ) ^ (-s) * (iteratedDeriv 1 (hurwitzKernel s) (r / N) * (N : ℝ)⁻¹)) r := by
    unfold loopArcG
    exact hcomp.const_mul _
  rw [hfull.deriv, iteratedDeriv_one]
  ring

/-- **Scaled first-derivative bound.** There is `C > 0` such that `|g_N'(r)| ≤ C r^{-s-1}` for
every `0 < r ≤ N/2`. -/
theorem norm_deriv_loopArcG_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ (N : ℝ) / 2 →
      |deriv (loopArcG s N) r| ≤ C * r ^ (-s - 1) := by
  obtain ⟨C, hC, hb⟩ := gradSplit_kernel_deriv_bound s hs0 hs1
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  refine ⟨C, hC, fun r hr hrR => ?_⟩
  have hrN : r < (N : ℝ) := lt_of_le_of_lt hrR (by linarith)
  have hx0 : 0 < r / N := div_pos hr hN
  have hx1 : r / N ≤ 3 / 4 := by
    rw [div_le_iff₀ hN]
    linarith
  have hbd := hb (r / N) (by rw [abs_of_pos hx0]; exact hx0)
    (by rw [abs_of_pos hx0]; exact hx1) 1 le_rfl (by norm_num)
  rw [iteratedDeriv_one, abs_of_pos hx0, Nat.cast_one] at hbd
  rw [deriv_loopArcG_eq s hs0 hs1 N hr hrN, abs_mul, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hN _), abs_of_pos (inv_pos.mpr hN)]
  -- Scale: `(r / N)^{-s-1} = r^{-s-1} N^{s+1}`, and `N^{-s} N^{-1} N^{s+1} = 1`.
  have hpow : (r / N) ^ (-s - 1) = r ^ (-s - 1) * (N : ℝ) ^ (s + 1) := by
    rw [show (-s - 1 : ℝ) = -(s + 1) by ring, Real.div_rpow hr.le hN.le,
      Real.rpow_neg hN.le, div_inv_eq_mul]
  have hmul : (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (s + 1)) = 1 := by
    have h1 : (N : ℝ) ^ (-s) * (N : ℝ) ^ (s + 1) = (N : ℝ) := by
      rw [← Real.rpow_add hN]
      norm_num
    calc (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (s + 1))
        = ((N : ℝ) ^ (-s) * (N : ℝ) ^ (s + 1)) * (N : ℝ)⁻¹ := by ring
      _ = 1 := by rw [h1, mul_inv_cancel₀ hN.ne']
  calc (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * |deriv (hurwitzKernel s) (r / N)|)
      ≤ (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (C * (r / N) ^ (-s - 1))) := by
        gcongr
    _ = C * ((N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (s + 1))) * r ^ (-s - 1) := by
        rw [hpow]
        ring
    _ = C * r ^ (-s - 1) := by rw [hmul, mul_one]

end Riesz1

end
end
