/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BoundarySelectionLawCyclic
public import Riesz1.Rigidity.BlockMoments
public import Riesz1.ToMathlib.LogConcave.EventSecondMoment

/-!
# Quantitative boundary selection

The numerical probability and exponential-tail bounds for a boundary-selected gap,
part of Theorem 1.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- A one-gap block is the nearest gap. -/
theorem boundary_blockLength_one_eq_gap {N : ℕ+} (X : Configuration N) (j : ℤ) :
    blockLength X j 1 = gap X j := by
  simp only [blockLength, gap, Nat.cast_one]

/-- The canonical finite preceding label gives exactly the original selected gap. -/
theorem gap_boundaryCyclicLabel (N : ℕ+) (a : UnitAddCircle) (ℓ : ℝ) (X : Configuration N) :
    gap X ((boundaryCyclicLabel N a ℓ X : Fin (N : ℕ)) : ℕ) = gap X (precedingLabel a ℓ X) := by
  obtain ⟨q, hq⟩ := (boundaryCyclicLabel_eq_iff N a ℓ X (boundaryCyclicLabel N a ℓ X)).mp rfl
  rw [hq]
  unfold gap
  rw [show ((boundaryCyclicLabel N a ℓ X : Fin (N : ℕ)) : ℤ) + (N : ℕ) * q + 1 =
      (((boundaryCyclicLabel N a ℓ X : Fin (N : ℕ)) : ℤ) + 1) + (N : ℕ) * q by ring,
    boundary_cyclicLift_add_mul, boundary_cyclicLift_add_mul]
  ring

/-- **Boundary selection**, part of Theorem 1:
every cyclic Borel gap-event family satisfies the numerical square-root bound.
The bound is chosen before all model parameters and boundary data. -/
theorem boundary_selection_probability_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters)
      (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (a : UnitAddCircle) (ℓ : ℝ)
      (A : Fin (N : ℕ) → Set (Fin (N : ℕ) → ℝ)),
      (∀ i, MeasurableSet (A i)) →
      (∀ i y, y ∈ gapSimplex N → ((fun r => y (finRotate (N : ℕ) r)) ∈ A i ↔ y ∈ A (finRotate (N : ℕ) i))) →
      (gibbsMeasure P N).real {X | gapVector X ∈ A (boundaryCyclicLabel N a ℓ X)} ≤
        C * ((gibbsMeasure P N).real (gapVector ⁻¹' A 0)) ^ (1 / (2 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := blockLength_moments 2 (by norm_num)
  refine ⟨B ^ (1 / (2 : ℝ)), Real.rpow_pos_of_pos hB _, ?_⟩
  intro hPL P N hN a ℓ A hA hcyc
  let := (modelWellDefined P N).2.2
  let : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  have hm := hb hPL P N hN 0 1 one_pos
  simp only [boundary_blockLength_one_eq_gap, Nat.cast_one] at hm
  simp only [Real.rpow_two, one_pow, mul_one] at hm
  have hsecond : (∫ X : Configuration N, gap X 0 ^ 2 ∂gibbsMeasure P N) ≤ B := by
    rw [← ofReal_integral_eq_lintegral_ofReal hm.1 (ae_of_all _ fun X => sq_nonneg (gap X 0))] at hm
    exact (ENNReal.ofReal_le_ofReal_iff hB.le).mp hm.2
  have hE := measurable_gapVector N (hA 0)
  have hid : IntegrableOn (fun X : Configuration N => gap X 0) (gapVector ⁻¹' A 0) (gibbsMeasure P N) :=
    (integrable_gap P N 0).integrableOn
  have he := boundary_selection_size_bias P N hN a ℓ A hA hcyc
  rw [← ofReal_integral_eq_lintegral_ofReal hid (ae_of_all _ fun X => (gap_pos X 0).le)] at he
  have hre : (gibbsMeasure P N).real {X | gapVector X ∈ A (boundaryCyclicLabel N a ℓ X)} =
      ∫ X in gapVector ⁻¹' A 0, gap X 0 ∂gibbsMeasure P N := by
    rw [Measure.real, he, ENNReal.toReal_ofReal (integral_nonneg (fun X => (gap_pos X 0).le))]
  rw [hre]
  exact (integral_on_event_le_second_moment (measurable_gap 0).aestronglyMeasurable
    (fun X => (gap_pos X 0).le) hm.1 hE).trans
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (integral_nonneg fun X => sq_nonneg (gap X 0)) hsecond (by norm_num))
        (Real.rpow_nonneg measureReal_nonneg _))

/-- **The selected-gap exponential tail**, the second claim of the boundary selection
bound in Theorem 1, with numerical constants. -/
theorem boundary_selection_gap_tail :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters)
      (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (a : UnitAddCircle) (ℓ : ℝ) (u : ℝ), 0 ≤ u →
      (gibbsMeasure P N).real {X | u < gap X (precedingLabel a ℓ X)} ≤ C * Real.exp (-c * u) := by
  obtain ⟨C, hC, hb⟩ := boundary_selection_probability_bound
  refine ⟨blockMomentExponent / 2, C * (3 : ℝ) ^ (1 / (2 : ℝ)),
    div_pos blockMomentExponent_pos (by norm_num), mul_pos hC (by positivity), ?_⟩
  intro hPL P N hN a ℓ u _hu
  let := (modelWellDefined P N).2.2
  let : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  let A := fun i : Fin (N : ℕ) => {y : Fin (N : ℕ) → ℝ | u < y i}
  have hA (i : Fin (N : ℕ)) : MeasurableSet (A i) := measurableSet_lt measurable_const (measurable_pi_apply i)
  have he := hb hPL P N hN a ℓ A hA (fun _ _ _ => Iff.rfl)
  have hs : {X : Configuration N | gapVector X ∈ A (boundaryCyclicLabel N a ℓ X)} =
      {X | u < gap X (precedingLabel a ℓ X)} := by
    ext X
    change u < gap X ((boundaryCyclicLabel N a ℓ X : Fin (N : ℕ)) : ℕ) ↔ u < gap X (precedingLabel a ℓ X)
    rw [gap_boundaryCyclicLabel]
  rw [hs] at he
  have ht := blockLength_upper_tail hPL P N hN 0 1 one_pos u
  simp only [boundary_blockLength_one_eq_gap, Nat.cast_one] at ht
  rw [one_mul] at ht
  have hprob : (gibbsMeasure P N).real (gapVector ⁻¹' A 0) =
      (gibbsMeasure P N).real {X | u < gap X 0} := rfl
  rw [hprob] at he
  calc (gibbsMeasure P N).real {X | u < gap X (precedingLabel a ℓ X)} ≤
      C * ((gibbsMeasure P N).real {X | u < gap X 0}) ^ (1 / (2 : ℝ)) := he
    _ ≤ C * (3 * Real.exp (-blockMomentExponent * u)) ^ (1 / (2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow measureReal_nonneg ht (by norm_num)) hC.le
    _ = C * (3 : ℝ) ^ (1 / (2 : ℝ)) * Real.exp (-(blockMomentExponent / 2) * u) := by
      rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
      have heq : (-blockMomentExponent * u) * (1 / (2 : ℝ)) = -(blockMomentExponent / 2) * u := by ring
      rw [heq, mul_assoc]

end Riesz1

end
