/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesDistanceTransport
public import Riesz1.Kernel.AdmissibleExamplesPositive
public import Riesz1.Kernel.AdmissibleExamples

/-!
# Admissibility of the distance powers

The complete distance-power case of the macroscopic examples: positive admissibility
with exponent equal to the power, the exact threshold for arbitrary positive powers,
and the endpoint obstructions. Together with the arc and Riesz-profile
constructions, these settle every macroscopic example.
-/

public section

open MeasureTheory

namespace Riesz1

/-- Every subcritical distance power is admissible at scale one with exponent `α=a`
and fixed marks zero and the antipode. -/
theorem admissible_distance_power (P : Parameters) {a : ℝ}
    (ha0 : 0 < a) (ha : a < P.val.2 / 2) :
    ∃ hf : MemLp (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) 2 volume,
      ∃ d : TestData, Admissible P ⟨fun x => dist x 0 ^ (-a), hf⟩
        (fun _ => ⟨1, zero_lt_one, le_rfl⟩) a d := by
  obtain ⟨hf, B, hB, hprim⟩ := primitiveRegularity_distance_power (parametersExponent P) ha0 ha
  obtain ⟨_, C, hC, htr⟩ := transportRegularity_distance_power P ha0 ha
  refine ⟨hf, ((P.val.2 - a) / 2, B, C, ⟨⟨2, by norm_num⟩, ![0, -(1 / 2)]⟩), ?_⟩
  exact ⟨by linarith [P.2.2.2], ha,
    by linarith [P.2.2.1], by linarith [P.2.2.1], hB, hC,
    Or.inl ⟨fun _ => rfl, hprim, htr⟩⟩

/-- The exact scale-one admissibility threshold for every positive distance power,
quantifying over every possible witnessing exponent and data. -/
theorem admissible_distance_power_iff (P : Parameters) {a : ℝ} (ha0 : 0 < a) :
    (∃ hf : MemLp (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) 2 volume,
      ∃ α : ℝ, ∃ d : TestData, Admissible P ⟨fun x => dist x 0 ^ (-a), hf⟩
        (fun _ => ⟨1, zero_lt_one, le_rfl⟩) α d) ↔ a < P.val.2 / 2 := by
  refine ⟨distance_power_admissible_only_if P ha0, fun ha => ?_⟩
  obtain ⟨hf, d, had⟩ := admissible_distance_power P ha0 ha
  exact ⟨hf, a, d, had⟩

/-- All distance-power assertions, including the excluded
endpoint and its failure of the Sobolev regularity supplied by admissibility. -/
theorem admissible_examples_distance_power (P : Parameters) :
    (∀ a : ℝ, 0 < a →
      ((∃ hf : MemLp (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) 2 volume,
        ∃ α : ℝ, ∃ d : TestData, Admissible P ⟨fun x => dist x 0 ^ (-a), hf⟩
          (fun _ => ⟨1, zero_lt_one, le_rfl⟩) α d) ↔ a < P.val.2 / 2)) ∧
    (¬ (∃ hf : MemLp
        (fun x : UnitAddCircle => ((dist x 0 ^ (-(P.val.2 / 2)) : ℝ) : ℂ)) 2 volume,
      ∃ α : ℝ, ∃ d : TestData, Admissible P ⟨fun x => dist x 0 ^ (-(P.val.2 / 2)), hf⟩
        (fun _ => ⟨1, zero_lt_one, le_rfl⟩) α d)) ∧
    ¬ CircleSobolev ((1 - P.val.2) / 2)
      (fun x : UnitAddCircle => ((dist x 0 ^ (-(P.val.2 / 2)) : ℝ) : ℂ)) :=
  ⟨fun _ ha0 => admissible_distance_power_iff P ha0,
    not_admissible_distance_power_endpoint P,
    not_circleSobolev_distance_power_endpoint (parametersExponent P)⟩

end Riesz1
