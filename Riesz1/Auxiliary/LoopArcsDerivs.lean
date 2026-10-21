/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsBounds
public import Riesz1.ToMathlib.HurwitzKernel.EndpointEstimates

/-!
# Scaled higher derivative bounds for the microscopic kernel

The microscopic kernel `g_N(r) = N^{-s} g(r / N)` (`loopArcG`) satisfies, for `0 < r < N`,
`g_N^{(k)}(r) = N^{-s-k} g^{(k)}(r / N)` for every order `k`. Combined with the derivative
bounds `|g^{(m)}(x)| ≤ C |x|^{-s-m}` (`m = 1, 2, 3`, `|x| ≤ 3/4`) of
`gradSplit_kernel_deriv_bound`, this gives the scale-invariant bound
`|g_N^{(m)}(r)| ≤ C r^{-s-m}` on `0 < r ≤ N/2`. The second and third derivatives enter the
arc representation `Λ` (through `g_N''(N/2)` and `g_N'''`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The scaled iterated derivatives of the microscopic kernel on `(0, N)`:
`g_N^{(k)}(r) = N^{-s} N^{-k} g^{(k)}(r / N)`, proved by induction on `k` with the chain rule on
the open interval `(0, 1)` of the kernel `g = hurwitzKernel s`. -/
theorem iteratedDeriv_loopArcG_eq (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (k : ℕ) :
    ∀ r : ℝ, 0 < r → r < (N : ℝ) →
      iteratedDeriv k (loopArcG s N) r
        = (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ k * iteratedDeriv k (hurwitzKernel s) (r / N) := by
  induction k with
  | zero =>
    intro r _ _
    simp [loopArcG]
  | succ k ih =>
    intro r hr0 hrN
    have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hev : iteratedDeriv k (loopArcG s N) =ᶠ[nhds r]
        fun x => (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ k * iteratedDeriv k (hurwitzKernel s) (x / N) := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨hr0, hrN⟩ : r ∈ Ioo (0 : ℝ) N)] with x hx
      exact ih x hx.1 hx.2
    have hx : r / (N : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hr0 hN, (div_lt_one hN).mpr hrN⟩
    have h1 := hasDerivAt_iteratedDeriv_open isOpen_Ioo
      (contDiffOn_hurwitzKernel_unit s hs0 hs1) k hx
    have h2 : HasDerivAt (fun x : ℝ => x / (N : ℝ)) ((N : ℝ)⁻¹) r := by
      simpa using (hasDerivAt_id r).div_const (N : ℝ)
    have hd : HasDerivAt (fun x : ℝ => (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ k
        * iteratedDeriv k (hurwitzKernel s) (x / N))
        ((N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ k * (iteratedDeriv (k + 1) (hurwitzKernel s) (r / N)
          * (N : ℝ)⁻¹)) r :=
      (h1.comp r h2).const_mul ((N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ k)
    rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]
    ring

/-- **Scaled derivative bound** for the microscopic kernel. For orders `1 ≤ m ≤ 3` there is one
constant `C`, depending only on `s`, with `|g_N^{(m)}(r)| ≤ C r^{-s-m}` for `0 < r ≤ N / 2`,
uniformly in `N`. -/
theorem norm_iteratedDeriv_loopArcG_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (m : ℕ), 1 ≤ m → m ≤ 3 → ∀ r : ℝ, 0 < r →
      r ≤ (N : ℝ) / 2 →
      |iteratedDeriv m (loopArcG s N) r| ≤ C * r ^ (-s - (m : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := gradSplit_kernel_deriv_bound s hs0 hs1
  refine ⟨C, hC, fun N m hm1 hm3 r hr hrR => ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hrN : r < (N : ℝ) := lt_of_le_of_lt hrR (by linarith)
  have hx0 : 0 < r / N := div_pos hr hN
  have hx1 : r / N ≤ 3 / 4 := by
    rw [div_le_iff₀ hN]
    linarith
  have hbd := hb (r / N) (by rw [abs_of_pos hx0]; exact hx0)
    (by rw [abs_of_pos hx0]; exact hx1) m hm1 hm3
  rw [abs_of_pos hx0] at hbd
  rw [iteratedDeriv_loopArcG_eq s hs0 hs1 N m r hr hrN]
  have hcoef : 0 ≤ (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ m := by positivity
  rw [abs_mul, abs_of_nonneg hcoef]
  -- the scaling identity `N^{-s} N^{-m} (r / N)^{-s-m} = r^{-s-m}`
  have hNz : (N : ℝ) ^ (-s - (m : ℝ)) = (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ m := by
    rw [show -s - (m : ℝ) = -s + -(m : ℝ) by ring, Real.rpow_add hN,
      Real.rpow_neg hN.le (m : ℝ), Real.rpow_natCast, inv_pow]
  have hpos : (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ m ≠ 0 := by positivity
  have hscale : (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ m * (r / N) ^ (-s - (m : ℝ))
      = r ^ (-s - (m : ℝ)) := by
    rw [Real.div_rpow hr.le hN.le, hNz]
    field_simp
  calc (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ m * |iteratedDeriv m (hurwitzKernel s) (r / N)|
      ≤ (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ m * (C * (r / N) ^ (-s - (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hbd hcoef
    _ = C * ((N : ℝ) ^ (-s) * ((N : ℝ)⁻¹) ^ m * (r / N) ^ (-s - (m : ℝ))) := by ring
    _ = C * r ^ (-s - (m : ℝ)) := by rw [hscale]

end Riesz1

end
end
