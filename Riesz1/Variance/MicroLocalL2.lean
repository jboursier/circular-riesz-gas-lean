/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.MicroLocalUnion
public import Riesz1.ToMathlib.MicroLocal.RealMoment

/-!
# Finite real second moments for microscopic tests

The `L²` and real-expectation forms of Lemma 5.3.
-/

public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

namespace Riesz1

theorem measurable_microLocal_square (N : ℕ+) (f : AddCircle (N : ℝ) → ℝ)
    (hf : Measurable f) : Measurable (fun X : Configuration N =>
      (∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2) := by
  have hc (i : Fin (N : ℕ)) : Measurable (fun X : Configuration N =>
      (((N : ℝ) * X.val i : ℝ) : AddCircle (N : ℝ))) :=
    (AddCircle.continuous_mk' _).measurable.comp
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_subtype_coe))
  simpa only [Function.comp_apply, Real.norm_eq_abs] using
    (Finset.measurable_sum univ fun i _ => (hf.comp (hc i)).norm).pow_const 2

/-- The `L²` form of Lemma 5.3, with square integrability
concluded before the real expectation is used. -/
theorem micro_local_l2 (P : Parameters) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      letI : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
      ∀ (I : Set (AddCircle (N : ℝ))) (_hmI : MeasurableSet I)
        (_hI : ∀ u ∈ I, ∀ v ∈ I, dist u v ≤ R)
        (f : AddCircle (N : ℝ) → ℝ) (_hf : Measurable f) (_hf2 : MemLp f 2 volume)
        (_hsupp : ∀ u ∉ I, f u = 0),
      Integrable (fun X : Configuration N =>
        (∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2) (gibbsMeasure P N) ∧
      (∫ X : Configuration N,
        (∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2 ∂gibbsMeasure P N) ≤
          C * ∫ u in I, f u ^ 2 := by
  obtain ⟨C, hC, h⟩ := micro_local P R
  refine ⟨C, hC, ?_⟩
  intro hPL N
  let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
  intro I hmI hI f hf hf2 hsupp
  exact integral_le_of_lintegral_bound_internal _ _ _ _
    (measurable_microLocal_square N f hf).aestronglyMeasurable
    (ae_of_all _ fun X => sq_nonneg _) hf2.integrable_sq.restrict
    (ae_of_all _ fun u => sq_nonneg _) C hC.le (h hPL N I hmI hI f hf hsupp)

/-- The finite-union `L²` form of Lemma 5.3, including
integrability and the real expectation bound. -/
theorem micro_local_union_l2 (P : Parameters) (R : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      letI : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
      ∀ (I : Fin m → Set (AddCircle (N : ℝ))) (_hmI : ∀ a, MeasurableSet (I a))
        (_hI : ∀ a, ∀ u ∈ I a, ∀ v ∈ I a, dist u v ≤ R)
        (f : AddCircle (N : ℝ) → ℝ) (_hf : Measurable f) (_hf2 : MemLp f 2 volume)
        (_hsupp : ∀ u ∉ ⋃ a, I a, f u = 0),
      Integrable (fun X : Configuration N =>
        (∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2) (gibbsMeasure P N) ∧
      (∫ X : Configuration N,
        (∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2 ∂gibbsMeasure P N) ≤
          C * ∫ u in ⋃ a, I a, f u ^ 2 := by
  obtain ⟨C, hC, h⟩ := micro_local_union P R m
  refine ⟨C, hC, ?_⟩
  intro hPL N
  let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
  intro I hmI hI f hf hf2 hsupp
  exact integral_le_of_lintegral_bound_internal _ _ _ _
    (measurable_microLocal_square N f hf).aestronglyMeasurable
    (ae_of_all _ fun X => sq_nonneg _) hf2.integrable_sq.restrict
    (ae_of_all _ fun u => sq_nonneg _) C hC.le (h hPL N I hmI hI f hf hsupp)

end Riesz1

end
