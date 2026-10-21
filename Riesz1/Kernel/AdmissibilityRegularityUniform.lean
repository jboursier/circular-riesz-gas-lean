/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityUniformCompact
public import Riesz1.Kernel.AdmissibilityRegularityFromAdmissible
public import Riesz1.Kernel.AdmissibilityRegularityConsequences

/-!
# Fourier decay from admissibility with the paper's quantifier order

For fixed profile data the Fourier constant is chosen before the scale sequence.
Together with the imported regularity, Sobolev and variance theorems, this closes
the uniform Fourier clause.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace Riesz1

/-- The Fourier-decay assertion, for both alternatives of the admissibility
assumption. One constant works for every sequence with the fixed data. -/
theorem admissible_coeff_decay_uniform (P : Parameters) (p : Profile) (α : ℝ)
    (d : TestData) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ (N : ℕ+) (k : ℤ),
        1 ≤ |2 * Real.pi * (k : ℝ) / (observationLength (ell N)).val| →
        ‖fourierCoeff (fun x => (testAtScale p (ell N) x : ℂ)) k‖ ≤
          K * (observationLength (ell N)).val⁻¹ *
            |2 * Real.pi * (k : ℝ) / (observationLength (ell N)).val| ^ (α - 1 + ε) := by
  classical
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d
  · obtain ⟨ell0, h0⟩ := hex
    obtain ⟨hα0, hα1, hη, _, hB, hC, _⟩ := h0
    have hm : ∃ K : ℝ, 0 < K ∧
        ((PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
          TransportRegularity P unitLength ⟨p.val, p.property⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
          ∀ k : ℤ, 1 ≤ |2 * Real.pi * (k : ℝ)| →
            ‖fourierCoeff (fun x => (p.val x : ℂ)) k‖ ≤
              K * |2 * Real.pi * (k : ℝ)| ^ (α - 1 + ε)) := by
      by_cases hmac : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
          TransportRegularity P unitLength ⟨p.val, p.property⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1
      · obtain ⟨K, hK, hk⟩ := coeff_decay_of_primitive_transportRegularity P unitLength
          d.1 d.2.1 hη hB.le ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1
          hα0 hα1 hC.le hmac.1 hmac.2 ε hε
        refine ⟨K, hK, fun _ k hfreq => ?_⟩
        have hf : 1 ≤ |2 * Real.pi * (k : ℝ) / unitLength.val| := by
          simpa only [unitLength, div_one] using hfreq
        have hd := hk k hf
        change ‖fourierCoeff (fun x => (p.val x : ℂ)) k‖ ≤ _ at hd
        simpa only [unitLength, inv_one, div_one, mul_one] using hd
      · exact ⟨1, zero_lt_one, fun hh => (hmac hh).elim⟩
    obtain ⟨Km, hKm, hmacro⟩ := hm
    have hc : ∃ K : ℝ, 0 < K ∧ ∀ hp : CompactProfile p, ∀ ell : Scales,
        Tendsto (fun n : ℕ => (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
              d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
        ∀ (a : Scale) (k : ℤ), 1 ≤ |2 * Real.pi * (k : ℝ) / (observationLength a).val| →
          ‖coeff (observationLength a)
            ⟨(fun x => (periodizedProfile p (observationLength a) x : ℂ)),
              complexL2Integrable _ _ (periodizedProfileL2 p a)⟩ k‖ ≤
            K * (observationLength a).val⁻¹ *
              |2 * Real.pi * (k : ℝ) / (observationLength a).val| ^ (α - 1 + ε) := by
      by_cases hp : CompactProfile p
      · obtain ⟨K, hK, hk⟩ := uniform_compact_profile_coeff_decay P p hp d.1 d.2.1 hη hB.le
          d.2.2.2.1 d.2.2.2.2 α d.2.2.1 hα0 hα1 hC.le ε hε
        exact ⟨K, hK, fun _ => hk⟩
      · exact ⟨1, zero_lt_one, fun hh => (hp hh).elim⟩
    obtain ⟨Kc, hKc, hcompact⟩ := hc
    refine ⟨max Km Kc, lt_of_lt_of_le hKm (le_max_left _ _), fun ell h N k hk => ?_⟩
    rcases h.2.2.2.2.2.2 with ⟨hell, hprim, hreg⟩ | ⟨hp, hell, hreg⟩
    · have hlen : (observationLength (ell N)).val = 1 := by simp only [observationLength, hell N, inv_one]
      simp only [hlen, inv_one, div_one, mul_one] at hk ⊢
      simp only [testAtScale, hell N, ite_true]
      exact (hmacro ⟨hprim, hreg⟩ k hk).trans (mul_le_mul_of_nonneg_right
        (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))
    · rw [testAtScale_coeff_eq_periodized]
      exact (hcompact hp ell hell hreg (ell N) k hk).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (inv_nonneg.mpr (observationLength (ell N)).property.le))
          (Real.rpow_nonneg (abs_nonneg _) _))
  · exact ⟨1, zero_lt_one, fun ell h => (hex ⟨ell, h⟩).elim⟩

end Riesz1
