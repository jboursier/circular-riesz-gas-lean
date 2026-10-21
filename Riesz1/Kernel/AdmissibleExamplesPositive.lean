/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesPrimitive
public import Riesz1.Kernel.AdmissibleExamplesRieszTransport
public import Riesz1.Kernel.AdmissibleExamplesIndicatorTransport
public import Riesz1.Frozen.Admissible

/-!
# Positive admissibility at scale one

The proper-arc and subcritical Riesz-profile assertions, using the `Admissible` predicate
and actual quantitative primitive and transport witnesses.
-/

public section

open MeasureTheory

namespace Riesz1

/-- Every proper nonempty arc is admissible at scale one with exponent zero.
All data are fixed before the particle index. -/
theorem admissible_arcIndicator (P : Parameters) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (c : UnitAddCircle) :
    ∃ d : TestData, Admissible P ⟨arcIndicator c a, memLp_arcIndicator c a⟩
      (fun _ => ⟨1, zero_lt_one, le_rfl⟩) 0 d := by
  obtain ⟨c, rfl⟩ := exists_real_coe c
  obtain ⟨B, hB, hprim⟩ := primitiveRegularity_arcIndicator (parametersExponent P) ha0 ha1
    (c : UnitAddCircle)
  obtain ⟨C, hC, htr⟩ := transportRegularity_arcIndicator P
  refine ⟨(P.val.2 / 2, B, C, ⟨⟨2, by norm_num⟩, ![c - a, c + a]⟩), ?_⟩
  exact ⟨by linarith [P.2.2.2], by linarith [P.2.2.1],
    by linarith [P.2.2.1], by linarith [P.2.2.1], hB, hC,
    Or.inl ⟨fun _ => rfl, hprim, htr a ha0 ha1 c⟩⟩

/-- All scale-one interval assertions: positive admissibility with exponent zero,
subcritical Sobolev membership, and exclusion from `H^(1/2)`. -/
theorem admissible_examples_indicator (P : Parameters) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (c : UnitAddCircle) :
    (∃ d : TestData, Admissible P ⟨arcIndicator c a, memLp_arcIndicator c a⟩
      (fun _ => ⟨1, zero_lt_one, le_rfl⟩) 0 d) ∧
      CircleSobolev ((1 - P.val.2) / 2) (fun x => (arcIndicator c a x : ℂ)) ∧
      ¬ CircleSobolev (1 / 2) (fun x => (arcIndicator c a x : ℂ)) :=
  ⟨admissible_arcIndicator P ha0 ha1 c,
    admissible_examples_indicator_sobolev (parametersExponent P) ha0 ha1 c⟩

/-- Every subcritical Riesz profile is admissible at scale one, with exponent equal to
its power. The L² certificate and all quantitative data are concluded. -/
theorem admissible_riesz (P : Parameters) (a : RieszExponent) (ha : a.val < P.val.2 / 2) :
    ∃ hf : MemLp (fun x : UnitAddCircle => (rieszRepresentative a x : ℂ)) 2 volume,
      ∃ d : TestData, Admissible P ⟨rieszRepresentative a, hf⟩
        (fun _ => ⟨1, zero_lt_one, le_rfl⟩) a.val d := by
  obtain ⟨hf, B, hB, hprim⟩ := primitiveRegularity_riesz (parametersExponent P) a ha
  obtain ⟨_, C, hC, htr⟩ := transportRegularity_riesz P a ha
  refine ⟨hf, ((P.val.2 - a.val) / 2, B, C, ⟨⟨1, zero_lt_one⟩, fun _ => 0⟩), ?_⟩
  exact ⟨by linarith [P.2.2.2, a.2.1], ha,
    by linarith [P.2.2.1], by linarith [P.2.2.1, a.2.1], hB, hC,
    Or.inl ⟨fun _ => rfl, hprim, htr⟩⟩

end Riesz1
