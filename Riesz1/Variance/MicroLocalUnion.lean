/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.MicroLocal

/-!
# A finite union of microscopic arcs

The finite-union clause of Lemma 5.3.
-/

public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

namespace Riesz1

/-- Finite-cover Cauchy--Schwarz for a sum of point evaluations. -/
theorem microLocal_union_pointwise {α ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : ι → Set α) (f : α → ℝ) (hsupp : ∀ u ∉ ⋃ a, I a, f u = 0) (x : κ → α) :
    (∑ i, |f (x i)|) ^ 2 ≤ (Fintype.card ι : ℝ) *
      ∑ a, (∑ i, |(I a).indicator f (x i)|) ^ 2 := by
  classical
  have hpoint (u : α) : |f u| ≤ ∑ a, |(I a).indicator f u| := by
    by_cases hu : u ∈ ⋃ a, I a
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hu
      calc
        |f u| = |(I a).indicator f u| := by rw [indicator_of_mem ha]
        _ ≤ _ := Finset.single_le_sum (f := fun b => |(I b).indicator f u|)
          (fun b _ => abs_nonneg _) (Finset.mem_univ a)
    · rw [hsupp u hu, abs_zero]
      exact sum_nonneg fun a _ => abs_nonneg _
  have hsum : (∑ i, |f (x i)|) ≤ ∑ a, ∑ i, |(I a).indicator f (x i)| := by
    rw [sum_comm]
    exact sum_le_sum fun i _ => hpoint (x i)
  calc
    _ ≤ (∑ a, ∑ i, |(I a).indicator f (x i)|) ^ 2 := by
      exact pow_le_pow_left₀ (sum_nonneg fun i _ => abs_nonneg _) hsum 2
    _ ≤ _ := by simpa only [card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι))
        (f := fun a => ∑ i, |(I a).indicator f (x i)|))

/-- **Finite unions**, Lemma 5.3. The constant is
chosen before the particle number, arc locations and test. No disjointness
of the sets is required, and the empty union is included. -/
theorem micro_local_union (P : Parameters) (R : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      letI : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
      ∀ (I : Fin m → Set (AddCircle (N : ℝ)))
        (_hmI : ∀ a, MeasurableSet (I a))
        (_hI : ∀ a, ∀ u ∈ I a, ∀ v ∈ I a, dist u v ≤ R)
        (f : AddCircle (N : ℝ) → ℝ) (_hf : Measurable f)
        (_hsupp : ∀ u ∉ ⋃ a, I a, f u = 0),
      (∫⁻ X : Configuration N, ENNReal.ofReal
        ((∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2) ∂gibbsMeasure P N) ≤
          ENNReal.ofReal C * ∫⁻ u in ⋃ a, I a, ENNReal.ofReal (f u ^ 2) := by
  obtain ⟨A, hA, hsingle⟩ := micro_local P R
  refine ⟨(m + 1 : ℝ) ^ 2 * A, by positivity, ?_⟩
  intro hPL N
  let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
  intro I hmI hI f hf hsupp
  let g := fun a : Fin m => (I a).indicator f
  have hg (a : Fin m) : Measurable (g a) := hf.indicator (hmI a)
  have hb (a : Fin m) := hsingle hPL N (I a) (hmI a) (hI a) (g a) (hg a)
    (fun u hu => indicator_of_notMem hu f)
  let B := ∫⁻ u in ⋃ a, I a, ENNReal.ofReal (f u ^ 2)
  have hmono (a : Fin m) : (∫⁻ u in I a, ENNReal.ofReal (g a u ^ 2)) ≤ B := by
    have he : (∫⁻ u in I a, ENNReal.ofReal (g a u ^ 2)) =
        ∫⁻ u in I a, ENNReal.ofReal (f u ^ 2) := by
      apply setLIntegral_congr_fun (hmI a)
      intro u hu
      change ENNReal.ofReal (g a u ^ 2) = ENNReal.ofReal (f u ^ 2)
      rw [show g a u = f u from indicator_of_mem hu f]
    rw [he]
    exact lintegral_mono_set (subset_iUnion I a)
  have hmeas (a : Fin m) : Measurable (fun X : Configuration N => ENNReal.ofReal
      ((∑ i : Fin (N : ℕ), |g a ((N : ℝ) * X.val i)|) ^ 2)) := by
    have hc (i : Fin (N : ℕ)) : Measurable (fun X : Configuration N =>
        (((N : ℝ) * X.val i : ℝ) : AddCircle (N : ℝ))) :=
      (AddCircle.continuous_mk' _).measurable.comp
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_subtype_coe))
    simpa only [Function.comp_apply, Real.norm_eq_abs] using
      ((Finset.measurable_sum univ fun i _ => ((hg a).comp (hc i)).norm).pow_const 2).ennreal_ofReal
  calc
    _ ≤ ∫⁻ X : Configuration N, ENNReal.ofReal ((m : ℝ) *
        ∑ a : Fin m, (∑ i : Fin (N : ℕ), |g a ((N : ℝ) * X.val i)|) ^ 2) ∂gibbsMeasure P N := by
      apply lintegral_mono
      intro X
      apply ENNReal.ofReal_le_ofReal
      simpa only [Fintype.card_fin] using microLocal_union_pointwise I f hsupp
        (fun i : Fin (N : ℕ) => (((N : ℝ) * X.val i : ℝ) : AddCircle (N : ℝ)))
    _ = ENNReal.ofReal (m : ℝ) * ∑ a : Fin m, ∫⁻ X : Configuration N, ENNReal.ofReal
        ((∑ i : Fin (N : ℕ), |g a ((N : ℝ) * X.val i)|) ^ 2) ∂gibbsMeasure P N := by
      simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg m),
        ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum _ (fun a _ => hmeas a)]
    _ ≤ ENNReal.ofReal (m : ℝ) * ∑ _a : Fin m, ENNReal.ofReal A * B := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply sum_le_sum
      intro a _
      exact (hb a).trans (mul_le_mul_of_nonneg_left (hmono a) zero_le)
    _ = ENNReal.ofReal ((m : ℝ) ^ 2 * A) * B := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_mul (sq_nonneg (m : ℝ)), ENNReal.ofReal_pow (Nat.cast_nonneg m),
        ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ hA.le
      nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- The finite-union clause of Lemma 5.3 for projected
intervals of length at most `R`. -/
theorem micro_local_arc_union (P : Parameters) (R : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      letI : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
      ∀ (a b : Fin m → ℝ) (_hR : ∀ j, b j - a j ≤ R)
        (f : AddCircle (N : ℝ) → ℝ) (_hf : Measurable f)
        (_hsupp : ∀ u ∉ ⋃ j, (fun x : ℝ => (x : AddCircle (N : ℝ))) '' Icc (a j) (b j),
          f u = 0),
      (∫⁻ X : Configuration N, ENNReal.ofReal
        ((∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2) ∂gibbsMeasure P N) ≤
          ENNReal.ofReal C * ∫⁻ u in ⋃ j,
            (fun x : ℝ => (x : AddCircle (N : ℝ))) '' Icc (a j) (b j),
              ENNReal.ofReal (f u ^ 2) := by
  obtain ⟨C, hC, h⟩ := micro_local_union P R m
  refine ⟨C, hC, ?_⟩
  intro hPL N
  let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
  intro a b hR f hf hsupp
  exact h hPL N _ (fun j => measurableSet_circle_interval _ _ _)
    (fun j => circle_interval_diameter _ _ _ R (hR j)) f hf hsupp

end Riesz1

end
