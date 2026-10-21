/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLPrekopa
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Whole-space exponential midpoint Prékopa–Leindler

The midpoint inequality assumes bounded functions of bounded support. For
continuous potentials whose exponentials are integrable, exhaustion by convex balls
removes both restrictions. The only external hypothesis is the Prékopa–Leindler
inequality `External.PrekopaLeindler`. This is an intermediate step toward the
Bakry–Émery criterion.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- Exponential midpoint Prékopa–Leindler on all of Euclidean space. -/
theorem prekopa_exp_integral (hPL : External.PrekopaLeindler) {d : ℕ} (hd : 0 < d)
    {A B C : EuclideanSpace ℝ (Fin d) → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C)
    (hiA : Integrable (fun x => Real.exp (A x)) volume)
    (hiB : Integrable (fun x => Real.exp (B x)) volume)
    (hiC : Integrable (fun x => Real.exp (C x)) volume)
    (hmid : ∀ x y, A x + B y ≤ 2 * C ((1 / 2 : ℝ) • (x + y))) :
    Real.sqrt ((∫ x, Real.exp (A x)) * ∫ x, Real.exp (B x)) ≤
      ∫ x, Real.exp (C x) := by
  let U (n : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 (n + 1)
  have hUn : ⋃ n, U n = univ := Metric.iUnion_ball_nat_succ _
  have hmono : Monotone U := fun i j hij =>
    Metric.ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hlim {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f volume) :
      Tendsto (fun n => ∫ x in U n, f x) atTop (𝓝 (∫ x, f x)) := by
    have hi : IntegrableOn f (⋃ n, U n) volume := by simpa only [hUn, integrableOn_univ]
    have ht := tendsto_setIntegral_of_monotone (s := U)
      (fun _ => measurableSet_ball) hmono hi
    rw [hUn, Measure.restrict_univ] at ht
    exact ht
  apply le_of_tendsto_of_tendsto
    (((hlim hiA).mul (hlim hiB)).sqrt) (hlim hiC)
  exact Eventually.of_forall fun n =>
    (bl_prekopa_integral hPL hd (Metric.isBounded_ball) Metric.isOpen_ball (convex_ball 0 _)
      A B C hA.continuousOn hB.continuousOn hC.continuousOn
      (fun x _ y _ => hmid x y)).2.2.2

end Riesz1

end
