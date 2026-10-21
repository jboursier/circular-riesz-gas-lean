/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesPositive
public import Riesz1.Kernel.AdmissibleExamplesPowers
public import Riesz1.Kernel.AdmissibleExamplesCompact

/-!
# Admissibility of the examples

The conjunction `Riesz1.admissible_examples_L236` collects, clause by clause, every assertion
on the admissibility of the examples. Each conjunct is proved by a named theorem:

* proper arcs at scale one with exponent zero: `Riesz1.admissible_arcIndicator`.
* fixed arcs supported in `(-1/2, 1/2)` on enlarged circles: `Riesz1.admissible_compact_arcIndicator`.
* the interval indicator lies in `H^{(1-s)/2}` and not in `H^{1/2}`:
  `Riesz1.admissible_examples_indicator`.
* the distance power `d(x,0)^{-a}` is admissible at scale one exactly when `a < s/2`, the
  endpoint `s/2` is excluded, and `d(x,0)^{-s/2}` is not in `H^{(1-s)/2}`:
  `Riesz1.admissible_examples_distance_power`.
* subcritical Riesz profiles `g_a`, `0 < a < s/2`: `Riesz1.admissible_riesz`.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- All assertions on the admissibility of the examples, for `0 < s < 1` and `β > 0` given by
the parameters. The scale-one clauses concern the constant sequence `ℓ_N = 1`. The enlarged-circle
clause concerns every shrinking scale sequence, with one `TestData` fixed before the sequence. -/
theorem admissible_examples_L236 (P : Parameters) :
    -- every proper nonempty arc, at scale one with exponent zero
    (∀ (c : UnitAddCircle) {a : ℝ}, 0 < a → a < 1 / 2 →
      ∃ d : TestData, Admissible P ⟨arcIndicator c a, memLp_arcIndicator c a⟩
        (fun _ => ⟨1, zero_lt_one, le_rfl⟩) 0 d) ∧
    -- a fixed arc supported in `(-1/2, 1/2)`, on every enlarged circle
    (∀ (c a : ℝ), 0 < a → |c| + a < 1 / 2 → ∃ d : TestData, ∀ ell : Scales,
      Tendsto (fun n : ℕ => (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) →
        Admissible P ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩
          ell 0 d) ∧
    -- proper interval indicators: membership in `H^{(1-s)/2}` and exclusion from `H^{1/2}`
    (∀ (c : UnitAddCircle) {a : ℝ}, 0 < a → a < 1 / 2 →
      CircleSobolev ((1 - P.val.2) / 2) (fun x => (arcIndicator c a x : ℂ)) ∧
      ¬ CircleSobolev (1 / 2) (fun x => (arcIndicator c a x : ℂ))) ∧
    -- the distance power: admissible at scale one exactly when `a < s/2`
    ((∀ a : ℝ, 0 < a →
      ((∃ hf : MemLp (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) 2 volume,
        ∃ α : ℝ, ∃ d : TestData, Admissible P ⟨fun x => dist x 0 ^ (-a), hf⟩
          (fun _ => ⟨1, zero_lt_one, le_rfl⟩) α d) ↔ a < P.val.2 / 2)) ∧
    -- the endpoint `a = s/2` is excluded, and `d^{-s/2}` is not in `H^{(1-s)/2}`
    (¬ (∃ hf : MemLp
        (fun x : UnitAddCircle => ((dist x 0 ^ (-(P.val.2 / 2)) : ℝ) : ℂ)) 2 volume,
      ∃ α : ℝ, ∃ d : TestData, Admissible P ⟨fun x => dist x 0 ^ (-(P.val.2 / 2)), hf⟩
        (fun _ => ⟨1, zero_lt_one, le_rfl⟩) α d)) ∧
    ¬ CircleSobolev ((1 - P.val.2) / 2)
      (fun x : UnitAddCircle => ((dist x 0 ^ (-(P.val.2 / 2)) : ℝ) : ℂ))) ∧
    -- subcritical Riesz profiles `g_a`, with exponent `a`, at scale one
    (∀ (a : RieszExponent), a.val < P.val.2 / 2 →
      ∃ hf : MemLp (fun x : UnitAddCircle => (rieszRepresentative a x : ℂ)) 2 volume,
        ∃ d : TestData, Admissible P ⟨rieszRepresentative a, hf⟩
          (fun _ => ⟨1, zero_lt_one, le_rfl⟩) a.val d) := by
  refine ⟨fun c a ha0 ha1 => admissible_arcIndicator P ha0 ha1 c,
    fun c a ha0 hca => admissible_compact_arcIndicator P ha0 hca,
    fun c a ha0 ha1 => ⟨(admissible_examples_indicator P ha0 ha1 c).2.1,
      (admissible_examples_indicator P ha0 ha1 c).2.2⟩,
    admissible_examples_distance_power P, ?_⟩
  exact fun a ha => admissible_riesz P a ha

end Riesz1

end
