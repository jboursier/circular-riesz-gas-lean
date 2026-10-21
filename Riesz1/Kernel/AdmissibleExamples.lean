/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesDistance
public import Riesz1.Kernel.AdmissibilityRegularity

/-!
# Sobolev assertions and necessary admissibility of the examples

This module proves both indicator Sobolev assertions, the sharp
Sobolev threshold for every positive distance-power exponent, and the necessary
admissibility condition, including exclusion of the critical endpoint.

The positive admissibility constructions are not proved by this module.
-/

public section

open MeasureTheory

namespace Riesz1

/-- Admissibility of a distance power at scale one forces `a < s/2`, independently of the
exponent and data used to witness admissibility (necessity).
The existential L² certificate is required by the profile carrier. -/
theorem distance_power_admissible_only_if (P : Parameters) {a : ℝ} (ha : 0 < a) :
    (∃ hf : MemLp (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) 2 volume,
      ∃ α : ℝ, ∃ d : TestData,
        Admissible P ⟨fun x => dist x 0 ^ (-a), hf⟩
          (fun _ => ⟨1, zero_lt_one, le_rfl⟩) α d) → a < P.val.2 / 2 := by
  rintro ⟨hf, α, d, had⟩
  have hSob := (admissibility_regularity.{0} P ⟨fun x => dist x 0 ^ (-a), hf⟩
    (fun _ => ⟨1, zero_lt_one, le_rfl⟩) α d had).2.1 (1 : ℕ+)
  have hSob' : CircleSobolev ((1 - P.val.2) / 2)
      (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) := by
    simpa only [testAtScale, ↓reduceIte] using hSob
  exact (circleSobolev_distance_power_real_iff ⟨P.val.2, P.2.2⟩ ha).mp hSob'

/-- No choice of admissibility exponent or data admits the critical distance power at
scale one (the excluded endpoint). -/
theorem not_admissible_distance_power_endpoint (P : Parameters) :
    ¬ (∃ hf : MemLp
        (fun x : UnitAddCircle => ((dist x 0 ^ (-(P.val.2 / 2)) : ℝ) : ℂ)) 2 volume,
      ∃ α : ℝ, ∃ d : TestData,
        Admissible P ⟨fun x => dist x 0 ^ (-(P.val.2 / 2)), hf⟩
          (fun _ => ⟨1, zero_lt_one, le_rfl⟩) α d) := by
  intro h
  have hh := distance_power_admissible_only_if P (by linarith [P.2.2.1]) h
  exact (lt_irrefl (P.val.2 / 2)) hh

end Riesz1
