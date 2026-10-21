/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.PrekopaLeindler
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Midpoint log-concavity of marginals

The midpoint marginal inequality follows from the midpoint Prékopa–Leindler inequality
`External.PrekopaLeindler`, which is taken as a hypothesis. No marginal concavity is
assumed. The other hypotheses are joint log-concavity, boundedness, and bounded support.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Joint log-concavity implies the geometric-mean midpoint inequality, also at zeros. -/
lemma sqrt_mul_le_midpoint_of_concaveOn_log {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hlog : ConcaveOn ℝ (Function.support F) (fun p => Real.log (F p))) (p q : E) :
    Real.sqrt (F p * F q) ≤ F ((1 / 2 : ℝ) • (p + q)) := by
  by_cases hp : F p = 0
  · simp only [hp, zero_mul, Real.sqrt_zero]
    exact hF _
  by_cases hq : F q = 0
  · simp only [hq, mul_zero, Real.sqrt_zero]
    exact hF _
  have hp' := lt_of_le_of_ne (hF p) (Ne.symm hp)
  have hq' := lt_of_le_of_ne (hF q) (Ne.symm hq)
  have hc : Convex ℝ (Function.support F) := hlog.1
  have hmem := hc (show p ∈ Function.support F from hp)
    (show q ∈ Function.support F from hq)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hconc := hlog.2
  have hm := hconc (show p ∈ Function.support F from hp)
    (show q ∈ Function.support F from hq)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simp only [← smul_add] at hmem hm
  have hmid : 0 < F ((1 / 2 : ℝ) • (p + q)) :=
    lt_of_le_of_ne (hF _) (Ne.symm hmem)
  apply (Real.log_le_log_iff (Real.sqrt_pos.mpr (mul_pos hp' hq')) hmid).mp
  rw [Real.log_sqrt (mul_pos hp' hq').le, Real.log_mul hp hq]
  simpa only [smul_eq_mul, one_div, div_eq_mul_inv, one_mul, mul_comm] using hm

/-- Bounded joint support gives bounded support for every fiber. -/
lemma isBounded_support_fiber {d : ℕ} (F : ℝ × EuclideanSpace ℝ (Fin d) → ℝ)
    (hs : Bornology.IsBounded (Function.support F)) (x : ℝ) :
    Bornology.IsBounded (Function.support (fun z => F (x, z))) := by
  have hb : Bornology.IsBounded (Prod.snd '' closure (Function.support F)) :=
    (hs.isCompact_closure.image continuous_snd).isBounded
  apply hb.subset
  intro z hz
  exact ⟨(x, z), subset_closure hz, rfl⟩

/-- The midpoint Prékopa inequality for every two marginal fibers. This concludes their
integrability before using their real integrals. -/
theorem marginal_midpoint_sqrt_le (hPL : External.PrekopaLeindler)
    (d : ℕ) (hd : 0 < d) (F : ℝ × EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : Measurable F) (hpos : ∀ p, 0 ≤ F p)
    (hbounded : Bornology.IsBounded (Set.range F))
    (hsupport : Bornology.IsBounded (Function.support F))
    (hlog : ConcaveOn ℝ (Function.support F) (fun p => Real.log (F p))) (x y : ℝ) :
    ∃ (_ : Integrable (fun z => F (x, z)) volume)
      (_ : Integrable (fun z => F (y, z)) volume)
      (_ : Integrable (fun z => F ((x + y) / 2, z)) volume),
      Real.sqrt ((∫ z, F (x, z)) * ∫ z, F (y, z)) ≤ ∫ z, F ((x + y) / 2, z) := by
  have hm (t : ℝ) : Measurable (fun z => F (t, z)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hb (t : ℝ) : Bornology.IsBounded (Set.range (fun z => F (t, z))) := by
    apply hbounded.subset
    rintro _ ⟨z, rfl⟩
    exact ⟨(t, z), rfl⟩
  apply hPL d hd _ _ _ (hm x) (hm y) (hm ((x + y) / 2))
    (fun z => hpos (x, z)) (fun z => hpos (y, z)) (fun z => hpos ((x + y) / 2, z))
    (hb x) (hb y) (hb ((x + y) / 2))
    (isBounded_support_fiber F hsupport x) (isBounded_support_fiber F hsupport y)
    (isBounded_support_fiber F hsupport ((x + y) / 2))
  intro u v
  have h := sqrt_mul_le_midpoint_of_concaveOn_log F hpos hlog (x, u) (y, v)
  convert h using 1
  congr 1
  apply Prod.ext
  · change (x + y) / 2 = (1 / 2 : ℝ) * (x + y)
    ring
  · rfl

end Riesz1

end
end
