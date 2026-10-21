/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroVarianceInput
public import Riesz1.Variance.AuxiliaryMixed
public import Riesz1.ToMathlib.VarianceFiniteSum

/-!
# Finite assembly of the far-piece variance

The variance-summation step of Lemma 5.3. It takes only the a priori input
of Lemma 5.2 as a hypothesis. All constants precede the tests,
their singular centers, the particle number, and the observation scale.
The tests are actual smooth functions on the circle.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1.Internal

/-- Apply the spatial a priori estimate to any fixed number of far
pieces, with a common envelope amplitude. Distinct singular centers
are allowed and the number of pieces can be zero. -/
theorem reg_micro_far_variance_of_input (hInput : RegMicroAPrioriInput)
    (P : Parameters) (lam ε : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ) * ℓ.val →
      ∀ (M : ℝ), 0 ≤ M → ∀ (c : Fin m → ℝ)
        (f : Fin m → Circle (observationLength ℓ) → ℝ),
        (∀ j, ContDiff ℝ 1 (fun u : ℝ => f j (u : Circle (observationLength ℓ)))) →
        (∀ j u, |deriv (fun t : ℝ => f j (t : Circle (observationLength ℓ))) u| ≤
          M * cutoffMajorant P.val.2 lam ((N : ℝ) * ℓ.val)
            |centralRep (observationLength ℓ) ((u - c j : ℝ) : Circle (observationLength ℓ))|) →
        ∃ hF : Integrable (fun X : Configuration N =>
            ∑ j : Fin m, ∑ i : Fin (N : ℕ),
              f j ((X.val i / ℓ.val : ℝ) : Circle (observationLength ℓ))) (gibbsMeasure P N),
          variance (gibbsMeasure P N)
            (fun X => ∑ j : Fin m, ∑ i : Fin (N : ℕ),
              f j ((X.val i / ℓ.val : ℝ) : Circle (observationLength ℓ))) hF ≤
            ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2)) := by
  obtain ⟨C, hC, hbound⟩ := hInput P lam hlam ε hε
  refine ⟨(m : ℝ) ^ 2 * C + 1, by positivity, fun N ℓ hK M hM c f hf hder => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  let F := fun j : Fin m => fun X : Configuration N =>
    ∑ i : Fin (N : ℕ), f j ((X.val i / ℓ.val : ℝ) : Circle (observationLength ℓ))
  have hLF (j : Fin m) : MemLp (F j) 2 (gibbsMeasure P N) := by
    have hc : Continuous (f j) :=
      (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 (hf j).continuous
    have hLp : MemLp (fun u => (f j u : ℂ)) 2 (arclength (observationLength ℓ)) := by
      have : Fact (0 < (observationLength ℓ).val) := ⟨(observationLength ℓ).property⟩
      have : IsFiniteMeasure (arclength (observationLength ℓ)) := by
        unfold arclength
        infer_instance
      obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
      exact MemLp.of_bound (Complex.continuous_ofReal.comp hc).aestronglyMeasurable A
        (ae_of_all _ fun z => by simpa using hA z (Set.mem_univ z))
    have hreal := memLp_real_of_complex (loopMasterPullback_memLp (observationLength ℓ) ⟨f j, hLp⟩)
    have he (X : Configuration N) : linearStatistic (loopMasterPullback (observationLength ℓ) (f j)) X =
        F j X := by
      unfold linearStatistic F
      apply Finset.sum_congr rfl
      intro i _
      rw [loopMasterPullback_coe]
      rfl
    simpa only [he] using memLp_linearStatistic P N hreal
  have hV (j : Fin m) : variance (gibbsMeasure P N) (F j) ((hLF j).integrable one_le_two) ≤
      ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2)) := by
    obtain ⟨hF, hv⟩ := hbound N ℓ hK M hM (c j) (f j) (hf j) (hder j)
    exact hv
  obtain ⟨hS, hsum⟩ := variance_finsetSum_le (gibbsMeasure P N) m F hLF
  refine ⟨hS, hsum.trans ?_⟩
  calc
    _ ≤ (m : ℝ≥0∞) * ∑ _j : Fin m,
        ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2)) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hV j) zero_le
    _ = ENNReal.ofReal ((m : ℝ) ^ 2 * C * M ^ 2 *
        ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (m : ℝ) ^ 2 * C * M ^ 2),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (m : ℝ) ^ 2 * C),
        ENNReal.ofReal_mul (sq_nonneg (m : ℝ)), ENNReal.ofReal_pow (Nat.cast_nonneg m),
        ENNReal.ofReal_natCast]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C * M ^ 2), ENNReal.ofReal_mul hC.le]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hp := Real.rpow_nonneg (show 0 ≤ (N : ℝ) * ℓ.val by linarith) (ε + max (2 * lam) P.val.2)
      nlinarith [mul_nonneg (sq_nonneg M) hp])

/-- The far-piece power in Lemma 5.3, with the smoothing factor
retained in the derivative envelope. The actual cutoff construction
remains to supply a family satisfying these analytic bounds. -/
theorem reg_micro_far_rate_of_input (hInput : RegMicroAPrioriInput)
    (P : Parameters) (α ε : ℝ) (hα : P.val.2 - 1 ≤ α) (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ) * ℓ.val →
      ∀ (M : ℝ), 0 ≤ M → ∀ (c : Fin m → ℝ)
        (f : Fin m → Circle (observationLength ℓ) → ℝ),
        (∀ j, ContDiff ℝ 1 (fun u : ℝ => f j (u : Circle (observationLength ℓ)))) →
        (∀ j u, |deriv (fun t : ℝ => f j (t : Circle (observationLength ℓ))) u| ≤
          (M * (((N : ℝ) * ℓ.val)⁻¹) ^ (1 - P.val.2)) *
            cutoffMajorant P.val.2 (1 - P.val.2 + α) ((N : ℝ) * ℓ.val)
              |centralRep (observationLength ℓ) ((u - c j : ℝ) : Circle (observationLength ℓ))|) →
        ∃ hF : Integrable (fun X : Configuration N =>
            ∑ j : Fin m, ∑ i : Fin (N : ℕ),
              f j ((X.val i / ℓ.val : ℝ) : Circle (observationLength ℓ))) (gibbsMeasure P N),
          variance (gibbsMeasure P N)
            (fun X => ∑ j : Fin m, ∑ i : Fin (N : ℕ),
              f j ((X.val i / ℓ.val : ℝ) : Circle (observationLength ℓ))) hF ≤
            ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ ε *
              (((N : ℝ) * ℓ.val) ^ (2 * α) + ((N : ℝ) * ℓ.val) ^ (3 * P.val.2 - 2))) := by
  obtain ⟨C, hC, hc⟩ := reg_micro_far_variance_of_input hInput P (1 - P.val.2 + α) ε
    (by linarith) hε m
  refine ⟨C, hC, fun N ℓ hK M hM c f hf hder => ?_⟩
  let K : ℝ := (N : ℝ) * ℓ.val
  have hK0 : 0 < K := by dsimp [K]; linarith
  obtain ⟨hF, hv⟩ := hc N ℓ hK (M * K⁻¹ ^ (1 - P.val.2)) (by positivity) c f hf hder
  refine ⟨hF, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hmax : K ^ (ε + max (2 * (1 - P.val.2 + α)) P.val.2) ≤
      K ^ ε * (K ^ (2 * (1 - P.val.2 + α)) + K ^ P.val.2) := by
    rw [Real.rpow_add hK0]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hK0.le _)
    rcases le_total (2 * (1 - P.val.2 + α)) P.val.2 with hs | hs
    · rw [max_eq_right hs]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hK0.le _)
    · rw [max_eq_left hs]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hK0.le _)
  have hp : (K⁻¹ ^ (1 - P.val.2)) ^ 2 *
      (K ^ ε * (K ^ (2 * (1 - P.val.2 + α)) + K ^ P.val.2)) =
      K ^ ε * (K ^ (2 * α) + K ^ (3 * P.val.2 - 2)) := by
    rw [Real.inv_rpow hK0.le, ← Real.rpow_neg hK0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hK0.le]
    simp only [mul_add, ← Real.rpow_add hK0]
    congr 2 <;> ring
  calc
    _ ≤ C * (M * K⁻¹ ^ (1 - P.val.2)) ^ 2 *
        (K ^ ε * (K ^ (2 * (1 - P.val.2 + α)) + K ^ P.val.2)) :=
      mul_le_mul_of_nonneg_left hmax (mul_nonneg hC.le (sq_nonneg _))
    _ = C * M ^ 2 * K ^ ε * (K ^ (2 * α) + K ^ (3 * P.val.2 - 2)) := by
      rw [mul_pow]
      calc
        _ = C * M ^ 2 * ((K⁻¹ ^ (1 - P.val.2)) ^ 2 *
            (K ^ ε * (K ^ (2 * (1 - P.val.2 + α)) + K ^ P.val.2))) := by ring
        _ = _ := by rw [hp]; ring

end Riesz1.Internal

end
