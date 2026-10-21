/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.MicroLocalUnit
public import Riesz1.ToMathlib.MicroLocal.CircleScale

/-!
# A microscopic local second moment

Lemma 5.3. All moments are nonnegative lower
integrals. No integrability is assumed in order to state an expectation.
-/

public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

namespace Riesz1

/-- **A microscopic local second moment**, Lemma 5.3.
The support can be any measurable set of diameter at most `R`. The
inequality holds for every measurable real test, hence in particular
for all measurable `L²` tests, and for every positive particle number. -/
theorem micro_local (P : Parameters) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      letI : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
      ∀ (I : Set (AddCircle (N : ℝ))) (_hmI : MeasurableSet I)
        (_hI : ∀ u ∈ I, ∀ v ∈ I, dist u v ≤ R)
        (f : AddCircle (N : ℝ) → ℝ) (_hf : Measurable f) (_hsupp : ∀ u ∉ I, f u = 0),
      (∫⁻ X : Configuration N, ENNReal.ofReal
        ((∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2) ∂gibbsMeasure P N) ≤
          ENNReal.ofReal C * ∫⁻ u in I, ENNReal.ofReal (f u ^ 2) := by
  obtain ⟨C, hC, hunit⟩ := micro_local_unit P R
  refine ⟨C, hC, ?_⟩
  intro hPL N
  let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
  intro I hmI hI f hf hsupp
  let e := AddCircle.equivAddCircle 1 (N : ℝ) one_ne_zero (by positivity)
  have he : Measurable e := (AddCircle.continuous_equivAddCircle ..).measurable
  have hdiam : ∀ u ∈ e ⁻¹' I, ∀ v ∈ e ⁻¹' I, dist u v ≤ R / (N : ℝ) := by
    intro u hu v hv
    have h := hI _ hu _ hv
    rw [circleScale_dist] at h
    exact (le_div_iff₀ (show (0 : ℝ) < N by positivity)).mpr (by nlinarith)
  have h := hunit hPL N (e ⁻¹' I) hdiam (f ∘ e) (hf.comp he)
    (fun u hu => hsupp _ hu)
  have hfun (X : Configuration N) (i : Fin (N : ℕ)) :
      (f ∘ e) (X.val i) = f ((N : ℝ) * X.val i) := by
    simp only [Function.comp_apply, e, AddCircle.equivAddCircle_apply_mk, inv_one, one_mul]
    rw [mul_comm]
  simp_rw [hfun] at h
  have hscale := lintegral_circleScale (N : ℝ) (fun u => ENNReal.ofReal (f u ^ 2))
    (hf.pow_const 2).ennreal_ofReal
  change (∫⁻ u : UnitAddCircle, ENNReal.ofReal ((f ∘ e) u ^ 2)) = _ at hscale
  rw [hscale] at h
  have hNZ : ENNReal.ofReal (N : ℝ) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hfull : (∫⁻ u, ENNReal.ofReal (f u ^ 2)) = ∫⁻ u in I, ENNReal.ofReal (f u ^ 2) := by
    rw [← lintegral_indicator hmI]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ I
    · simp only [indicator_of_mem hu]
    · simp only [indicator_of_notMem hu, hsupp u hu, zero_pow (by norm_num : 2 ≠ 0),
        ENNReal.ofReal_zero]
  have hc : ENNReal.ofReal C * ENNReal.ofReal (N : ℝ) * (ENNReal.ofReal (N : ℝ))⁻¹ =
      ENNReal.ofReal C := by
    rw [mul_assoc, ENNReal.mul_inv_cancel hNZ ENNReal.ofReal_ne_top, mul_one]
  simpa only [← mul_assoc, hc, hfull] using h

/-- The stated arc form of Lemma 5.3. Arcs are projected real
intervals. Arbitrary endpoints, zero-length arcs, and full-circle arcs are
included. The measurable-test formulation includes every real `L²` test. -/
theorem micro_local_arc (P : Parameters) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
      letI : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
      ∀ (a b : ℝ) (_hR : b - a ≤ R) (f : AddCircle (N : ℝ) → ℝ)
        (_hf : Measurable f)
        (_hsupp : ∀ u ∉ (fun x : ℝ => (x : AddCircle (N : ℝ))) '' Icc a b, f u = 0),
      (∫⁻ X : Configuration N, ENNReal.ofReal
        ((∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2) ∂gibbsMeasure P N) ≤
          ENNReal.ofReal C * ∫⁻ u in (fun x : ℝ => (x : AddCircle (N : ℝ))) '' Icc a b,
            ENNReal.ofReal (f u ^ 2) := by
  obtain ⟨C, hC, h⟩ := micro_local P R
  refine ⟨C, hC, ?_⟩
  intro hPL N
  let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
  intro a b hR f hf hsupp
  exact h hPL N _ (measurableSet_circle_interval _ a b)
    (circle_interval_diameter _ a b R hR) f hf hsupp

end Riesz1

end
