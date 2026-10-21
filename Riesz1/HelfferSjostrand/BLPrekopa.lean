/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.PrekopaLeindler
public import Riesz1.HelfferSjostrand.BLNormalization

/-!
# Prékopa–Leindler on a bounded convex domain

The Prékopa–Leindler inequality `External.PrekopaLeindler` is used only as an explicit
hypothesis. Zero extension turns continuous exponential functions on a compact closure into bounded
Borel functions of bounded support. This supplies the integral comparison
used by the Brascamp–Lieb second variation.
-/

public section

noncomputable section

open MeasureTheory

namespace Riesz1

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}

/-- Zero extension of a continuous function on the closure is Borel. -/
theorem bl_measurable_indicator {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (ho : IsOpen U) (hf : ContinuousOn f (closure U)) : Measurable (U.indicator f) := by
  classical
  exact (hf.mono subset_closure).measurable_piecewise continuousOn_const ho.measurableSet

/-- Zero extension has bounded range when the domain has compact closure. -/
theorem bl_indicator_bounded_range {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Bornology.IsBounded U) (hf : ContinuousOn f (closure U)) :
    Bornology.IsBounded (Set.range (U.indicator f)) := by
  classical
  obtain ⟨C, hC⟩ := (hU.isCompact_closure.image_of_continuousOn hf).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max C 0, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx]
    exact (hC _ (Set.mem_image_of_mem f (subset_closure hx))).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

/-- The exponential midpoint inequality on a bounded convex domain, with no
boundary regularity needed. All three integrabilities are concluded. -/
theorem bl_prekopa_integral (hPL : Riesz1.External.PrekopaLeindler) (hd : 0 < d)
    (hU : Bornology.IsBounded U) (ho : IsOpen U) (hc : Convex ℝ U)
    (A B C : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : ContinuousOn A (closure U)) (hB : ContinuousOn B (closure U))
    (hC : ContinuousOn C (closure U))
    (hmid : ∀ x ∈ U, ∀ y ∈ U,
      A x + B y ≤ 2 * C ((1 / 2 : ℝ) • (x + y))) :
    IntegrableOn (fun x => Real.exp (A x)) U volume ∧
      IntegrableOn (fun x => Real.exp (B x)) U volume ∧
      IntegrableOn (fun x => Real.exp (C x)) U volume ∧
      Real.sqrt ((∫ x in U, Real.exp (A x)) * ∫ x in U, Real.exp (B x)) ≤
        ∫ x in U, Real.exp (C x) := by
  classical
  let a := U.indicator (fun x => Real.exp (A x))
  let b := U.indicator (fun x => Real.exp (B x))
  let c := U.indicator (fun x => Real.exp (C x))
  have hAe := Real.continuous_exp.comp_continuousOn hA
  have hBe := Real.continuous_exp.comp_continuousOn hB
  have hCe := Real.continuous_exp.comp_continuousOn hC
  have hn (D : EuclideanSpace ℝ (Fin d) → ℝ) (x) :
      0 ≤ U.indicator (fun y => Real.exp (D y)) x :=
    Set.indicator_nonneg (fun y _ => (Real.exp_pos (D y)).le) x
  obtain ⟨ha, hb, hci, hineq⟩ := hPL d hd a b c
    (bl_measurable_indicator ho hAe) (bl_measurable_indicator ho hBe)
    (bl_measurable_indicator ho hCe) (hn A) (hn B) (hn C)
    (bl_indicator_bounded_range hU hAe) (bl_indicator_bounded_range hU hBe)
    (bl_indicator_bounded_range hU hCe)
    (hU.subset Set.support_indicator_subset) (hU.subset Set.support_indicator_subset)
    (hU.subset Set.support_indicator_subset) (by
      intro x y
      by_cases hx : x ∈ U
      · by_cases hy : y ∈ U
        · have hz : (1 / 2 : ℝ) • (x + y) ∈ U := by
            simpa only [smul_add] using hc hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
          dsimp [a, b, c]
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
          apply Real.sqrt_le_iff.mpr
          refine ⟨(Real.exp_pos _).le, ?_⟩
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          exact Real.exp_le_exp.mpr (hmid x hx y hy)
        · simp only [b, Set.indicator_of_notMem hy, mul_zero, Real.sqrt_zero]
          exact hn C _
      · simp only [a, Set.indicator_of_notMem hx, zero_mul, Real.sqrt_zero]
        exact hn C _)
  refine ⟨bl_integrableOn_of_continuousOn_closure hU ho hAe,
    bl_integrableOn_of_continuousOn_closure hU ho hBe,
    bl_integrableOn_of_continuousOn_closure hU ho hCe, ?_⟩
  simpa only [a, b, c, integral_indicator ho.measurableSet] using hineq

end Riesz1

end
