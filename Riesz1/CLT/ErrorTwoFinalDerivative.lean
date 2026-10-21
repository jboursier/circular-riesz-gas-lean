/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoFinalStatement

/-!
# The complete derivative variance in the loop-error theorem

The second variance in the proof of the second error bound in Theorem 3, for both branches of
the admissibility predicate `Admissible`. The endpoint is included by a
fixed exponent increase absorbed in the requested loss. The only
conditional proof input is the a-priori conclusion.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1.Internal

/-- The second variance in the proof of the second error bound in Theorem 3, uniform before the
scale sequence and including `α = s - 1`. In fact `K₀ = 1` suffices. -/
theorem errorTwo_derivative_of_input (hAP : APrioriConclusion)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
        ErrorTwoDerivativeConclusion hρ P p α (2 * τ) C (ell N) N := by
  classical
  by_cases hdata : (P.val.2 - 1 ≤ α ∧ α < P.val.2 / 2) ∧
      (0 < d.1 ∧ d.1 < P.val.2 ∧ 0 < d.2.1 ∧ 0 < d.2.2.1)
  swap
  · exact ⟨1, one_pos, fun ell hadm =>
      absurd ⟨⟨hadm.1, hadm.2.1⟩, hadm.2.2.1, hadm.2.2.2.1,
        hadm.2.2.2.2.1, hadm.2.2.2.2.2.1⟩ hdata⟩
  obtain ⟨⟨hα0, hα1⟩, hη, _, hB, hC₀⟩ := hdata
  let η := min (τ / 4) ((P.val.2 / 2 - α) / 2)
  have hηp : 0 < η := lt_min (by positivity) (by linarith)
  have hητ : η ≤ τ / 4 := min_le_left _ _
  have hηα : η ≤ (P.val.2 / 2 - α) / 2 := min_le_right _ _
  have hα'0 : P.val.2 - 1 < α + η := by linarith
  have hα'1 : α + η < P.val.2 / 2 := by linarith
  have hloss : τ + 2 * η ≤ 2 * τ := by linarith
  have hm : ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      (PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
        TransportRegularity P unitLength ⟨p.val, p.property⟩
          d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      (∀ N, (ell N).val = 1) → ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
        ErrorTwoDerivativeConclusion hρ P p (α + η) τ C (ell N) N := by
    by_cases hU : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
        TransportRegularity P unitLength ⟨p.val, p.property⟩
          d.2.2.2.1 d.2.2.2.2 α d.2.2.1
    swap
    · exact ⟨1, one_pos, fun _ hU' => absurd hU' hU⟩
    obtain ⟨C, hC, hbound⟩ := errorTwo_macro_derivative_variance hAP P p d α (α + η) τ hτ
      hη hB.le hC₀.le hα0 hα1 (by linarith) hα'0 hα'1 hU.1 hU.2 hρ
    exact ⟨C, hC, fun ell _ hone N hK => hbound N (ell N) (hone N) hK⟩
  have hc : ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, CompactProfile p →
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (nhds 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
        ErrorTwoDerivativeConclusion hρ P p (α + η) τ C (ell N) N := by
    by_cases hp : CompactProfile p
    swap
    · exact ⟨1, one_pos, fun _ hp' => absurd hp' hp⟩
    obtain ⟨C, hC, hbound⟩ := errorTwo_compact_derivative_variance hAP P p hp d α (α + η) τ
      hτ hη hB.le hC₀.le hα0 hα1 (by linarith) hα'0 hα'1 hρ
    exact ⟨C, hC, fun ell _ hell hreg N hK => hbound ell hell hreg N hK⟩
  obtain ⟨Cm, hCm, hm⟩ := hm
  obtain ⟨Cc, hCc, hc⟩ := hc
  refine ⟨Cm + Cc, by positivity, fun ell hadm N hK => ?_⟩
  rcases hadm.2.2.2.2.2.2 with ⟨hone, hprim, hreg⟩ | ⟨hp, hell, hreg⟩
  · exact errorTwo_derivative_enlarge hρ P p (ell N) N hK hηp.le hloss hCm.le
      (by linarith) (hm ell ⟨hprim, hreg⟩ hone N hK)
  · exact errorTwo_derivative_enlarge hρ P p (ell N) N hK hηp.le hloss hCc.le
      (by linarith) (hc ell hp hell hreg N hK)

end Riesz1.Internal
