/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.MicroLocalUnion
public import Riesz1.Variance.RegMicroKernelComplete
public import Riesz1.ToMathlib.CirclePullback
public import Riesz1.ToMathlib.SizeBiasedVariance
public import Riesz1.Gibbs.FluctuationMoments

/-!
# Variance on a finite union of microscopic arcs

The local second-moment step of Lemma 5.3, including
the bounded-scale argument and `N = 1`. The constant precedes the test,
the particle number and all arc centers. The bound is for the
extended variance and concludes integrability of the statistic.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

/-- The near-piece variance is controlled by its microscopic `L²` mass.
The arcs may overlap, be empty, or cover the entire circle. -/
theorem reg_micro_local_variance (P : Parameters) (R : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (hPL : External.PrekopaLeindler) (N : ℕ+),
      letI : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
      ∀ (a b : Fin m → ℝ), (∀ j, b j - a j ≤ R) →
      ∀ f : AddCircle (N : ℝ) → ℝ, Measurable f →
      MemLp (fun u => (f u : ℂ)) 2 volume →
      (∀ u ∉ ⋃ j, (fun t : ℝ => (t : AddCircle (N : ℝ))) '' Icc (a j) (b j), f u = 0) →
      ∃ hF : Integrable (fun X : Configuration N =>
          ∑ i : Fin (N : ℕ), f ((N : ℝ) * X.val i)) (gibbsMeasure P N),
        variance (gibbsMeasure P N)
          (fun X => ∑ i : Fin (N : ℕ), f ((N : ℝ) * X.val i)) hF ≤
          ENNReal.ofReal C * ∫⁻ u in ⋃ j,
            (fun t : ℝ => (t : AddCircle (N : ℝ))) '' Icc (a j) (b j),
              ENNReal.ofReal (f u ^ 2) := by
  obtain ⟨C, hC, hlocal⟩ := micro_local_arc_union P R m
  refine ⟨C, hC, ?_⟩
  intro hPL N
  let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
  intro a b hR f hfm hf hsupp
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  let L : Length := ⟨N, by exact_mod_cast N.pos⟩
  let g : UnitAddCircle → ℝ := fun z =>
    f (AddCircle.equivAddCircle 1 (N : ℝ) one_ne_zero (by positivity) z)
  have hg : MemLp g 2 volume := by
    have h := memLp_comp_dilation L (fun u => (f u : ℂ)) hf
    simpa [g, L] using h.re
  have he (X : Configuration N) : linearStatistic g X =
      ∑ i : Fin (N : ℕ), f ((N : ℝ) * X.val i) := by
    unfold linearStatistic
    apply Finset.sum_congr rfl
    intro i _
    simp only [g, AddCircle.equivAddCircle_apply_mk, inv_one, one_mul]
    rw [mul_comm]
  have hF : MemLp (fun X : Configuration N =>
      ∑ i : Fin (N : ℕ), f ((N : ℝ) * X.val i)) 2 (gibbsMeasure P N) := by
    simpa only [he] using memLp_linearStatistic P N hg
  refine ⟨hF.integrable one_le_two, ?_⟩
  apply (variance_le_lintegral_sq_sub (gibbsMeasure P N) hF 0).trans
  calc
    _ ≤ ∫⁻ X : Configuration N, ENNReal.ofReal
        ((∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)|) ^ 2) ∂gibbsMeasure P N := by
      apply lintegral_mono
      intro X
      apply ENNReal.ofReal_le_ofReal
      simp only [sub_zero]
      have hb : |∑ i : Fin (N : ℕ), f ((N : ℝ) * X.val i)| ≤
          ∑ i : Fin (N : ℕ), |f ((N : ℝ) * X.val i)| := Finset.abs_sum_le_sum_abs _ _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ ≤ _ := hlocal hPL N a b hR f hfm hsupp

/-- A uniformly bounded near piece has bounded variance, independently
of the particle number and all arc centers. This applies to the
negative-exponent error envelope after microscopic rescaling. -/
theorem reg_micro_bounded_near_variance (P : Parameters) (R : ℝ) (hR : 0 ≤ R) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (hPL : External.PrekopaLeindler) (N : ℕ+),
      letI : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
      ∀ (a b : Fin m → ℝ), (∀ j, b j - a j ≤ R) →
      ∀ (A : ℝ), 0 ≤ A → ∀ f : AddCircle (N : ℝ) → ℝ, Measurable f →
      (∀ u, |f u| ≤ A) →
      (∀ u ∉ ⋃ j, (fun t : ℝ => (t : AddCircle (N : ℝ))) '' Icc (a j) (b j), f u = 0) →
      ∃ hF : Integrable (fun X : Configuration N =>
          ∑ i : Fin (N : ℕ), f ((N : ℝ) * X.val i)) (gibbsMeasure P N),
        variance (gibbsMeasure P N)
          (fun X => ∑ i : Fin (N : ℕ), f ((N : ℝ) * X.val i)) hF ≤ ENNReal.ofReal (C * A ^ 2) := by
  obtain ⟨C, hC, hlocal⟩ := reg_micro_local_variance P R m
  refine ⟨C * ((m : ℝ) * (2 * R)) + 1, by positivity, ?_⟩
  intro hPL N
  let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
  intro a b hab A hA f hf hbound hsupp
  let I (j : Fin m) := (fun t : ℝ => (t : AddCircle (N : ℝ))) '' Icc (a j) (b j)
  have hvol (j : Fin m) : volume (I j) ≤ ENNReal.ofReal (2 * R) := by
    have hsub : I j ⊆ Metric.closedBall (a j : AddCircle (N : ℝ)) R := by
      rintro u ⟨t, ht, rfl⟩
      apply (show dist (t : AddCircle (N : ℝ)) (a j : AddCircle (N : ℝ)) ≤ |t - a j| from ?_).trans
      · exact (abs_of_nonneg (by linarith [ht.1])).le.trans (by linarith [ht.2, hab j])
      · rw [dist_eq_norm, ← AddCircle.coe_sub]
        exact QuotientAddGroup.norm_mk_le_norm
    calc
      _ ≤ volume (Metric.closedBall (a j : AddCircle (N : ℝ)) R) := measure_mono hsub
      _ = ENNReal.ofReal (min (N : ℝ) (2 * R)) := AddCircle.volume_closedBall _ _
      _ ≤ _ := ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hmass : volume (⋃ j, I j) ≤ ENNReal.ofReal ((m : ℝ) * (2 * R)) := by
    calc
      _ ≤ ∑ j, volume (I j) := measure_iUnion_fintype_le volume I
      _ ≤ ∑ _j : Fin m, ENNReal.ofReal (2 * R) := Finset.sum_le_sum fun j _ => hvol j
      _ = _ := by simp [ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  have hL : MemLp (fun u => (f u : ℂ)) 2 volume :=
    MemLp.of_bound (Complex.continuous_ofReal.measurable.comp hf).aestronglyMeasurable A
      (ae_of_all _ fun u => by simpa using hbound u)
  obtain ⟨hF, hv⟩ := hlocal hPL N a b hab f hf hL hsupp
  refine ⟨hF, hv.trans ?_⟩
  have hi : (∫⁻ u in ⋃ j, I j, ENNReal.ofReal (f u ^ 2)) ≤
      ENNReal.ofReal (A ^ 2) * ENNReal.ofReal ((m : ℝ) * (2 * R)) := by
    calc
      _ ≤ ∫⁻ _u in ⋃ j, I j, ENNReal.ofReal (A ^ 2) := by
        apply lintegral_mono
        intro u
        apply ENNReal.ofReal_le_ofReal
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound u) 2
      _ = ENNReal.ofReal (A ^ 2) * volume (⋃ j, I j) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass zero_le
  calc
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (A ^ 2) *
        ENNReal.ofReal ((m : ℝ) * (2 * R))) := mul_le_mul_of_nonneg_left hi zero_le
    _ = ENNReal.ofReal (C * ((m : ℝ) * (2 * R)) * A ^ 2) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C * ((m : ℝ) * (2 * R))),
        ENNReal.ofReal_mul hC.le]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg A])

end Riesz1.Internal

end
