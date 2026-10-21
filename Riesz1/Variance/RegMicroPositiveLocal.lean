/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroNearFarLocal
public import Riesz1.ToMathlib.CircleSingularSquareMass
public import Riesz1.ToMathlib.Inversion.IntegralBounds

/-!
# Unbounded positive-exponent tests on microscopic arcs

The local second moment applies to the singular envelope itself. The
result derives square integrability, rather than requiring bounded tests.
This is the positive-exponent local step of Lemma 5.3.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1.Internal

/-- Uniform local variance for the positive singular envelope on `N𝕋`.
The constant precedes every test, mark and particle number, including one. -/
theorem reg_micro_positive_local_variance (P : Parameters) (m : ℕ) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (hPL : External.PrekopaLeindler) (N : ℕ+),
      let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
      ∀ (a : Fin m → ℝ) (A : ℝ), 0 ≤ A →
      ∀ f : AddCircle (N : ℝ) → ℝ, Measurable f →
      (∀ᵐ u ∂volume, |f u| ≤ A *
        (1 + ∑ j, dist u (a j : AddCircle (N : ℝ)) ^ (-α))) →
      (∀ u ∉ ⋃ j, Metric.closedBall (a j : AddCircle (N : ℝ)) 4, f u = 0) →
      ∃ hF : Integrable (fun X : Configuration N =>
          ∑ i : Fin (N : ℕ), f ((N : ℝ)*X.val i)) (gibbsMeasure P N),
        variance (gibbsMeasure P N)
          (fun X => ∑ i : Fin (N : ℕ), f ((N : ℝ)*X.val i)) hF ≤
            ENNReal.ofReal (D*A^2) := by
  classical
  obtain ⟨C, hC, hb⟩ := reg_micro_local_variance P 8 m
  let B : ℝ := 8*m
  let T : ℝ := ((m : ℝ)+1)*(B+(m : ℝ)*(2/(1-2*α)+B))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hden : 0 < 1-2*α := by linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨C*T+1, by positivity, fun hPL N => ?_⟩
  dsimp only
  let : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩
  intro a A hA f hf henv hsupp
  let S := ⋃ j, Metric.closedBall (a j : AddCircle (N : ℝ)) 4
  have hSm : MeasurableSet S := MeasurableSet.iUnion fun _ => measurableSet_closedBall
  have hmass : volume S ≤ ENNReal.ofReal B := by
    calc
      _ ≤ ∑ j, volume (Metric.closedBall (a j : AddCircle (N : ℝ)) 4) :=
        measure_iUnion_fintype_le volume _
      _ ≤ ∑ _j : Fin m, ENNReal.ofReal (8 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [AddCircle.volume_closedBall]
        exact ENNReal.ofReal_le_ofReal ((min_le_right (N : ℝ) (2*(4 : ℝ))).trans (by norm_num))
      _ = _ := by simp [B, ENNReal.ofReal_mul, mul_comm]
  have hiS : (∫⁻ u in S, ENNReal.ofReal (f u^2)) ≤ ENNReal.ofReal (T*A^2) := by
    have hh := lintegral_circle_sq_le_of_singular_envelope hα0 hα1 zero_lt_one hA hB m
      (fun j => (a j : AddCircle (N : ℝ))) S (by simpa using hmass) f
      (by simpa using ae_restrict_of_ae henv)
    simpa only [Real.one_rpow, mul_one, one_mul, T, mul_assoc, mul_left_comm, mul_comm] using hh
  have hfull : (∫⁻ u, ENNReal.ofReal (f u^2)) = ∫⁻ u in S, ENNReal.ofReal (f u^2) := by
    rw [← lintegral_indicator hSm]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, hsupp u hu]
      norm_num
  have hreal : MemLp f 2 volume :=
    (inversion_memLp_two_of_secondMoment hf (mul_nonneg hT (sq_nonneg A))
      (hfull.trans_le hiS)).1
  have hcomplex : MemLp (fun u => (f u : ℂ)) 2 volume := by
    exact hreal.ofReal
  have hsets : (⋃ j, (fun t : ℝ => (t : AddCircle (N : ℝ))) '' Icc (a j-4) (a j+4)) = S := by
    simp only [S, circle_closedBall_eq_image_interval]
  obtain ⟨hF, hv⟩ := hb hPL N (fun j => a j-4) (fun j => a j+4)
    (fun j => by linarith) f hf hcomplex (by simpa only [hsets] using hsupp)
  refine ⟨hF, hv.trans ?_⟩
  rw [hsets]
  calc
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (T*A^2) :=
      mul_le_mul_of_nonneg_left hiS zero_le
    _ = ENNReal.ofReal (C*T*A^2) := by rw [← ENNReal.ofReal_mul hC.le]; congr 1; ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg A])

end Riesz1.Internal
