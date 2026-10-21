/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlFinalPieces

/-!
# The compact loop bound after fixing a scale sequence

An internal consequence of the decomposition of Proposition 5.9 and the
all-particle envelope bound. Its coefficient is chosen after the scale
sequence, so this theorem does not assert the uniform quantifier order
required by Proposition 5.9.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace Riesz1.Internal

/-- The compact decomposition suffices for each fixed shrinking
sequence. The strict exponent and sequence dependence are explicit. -/
theorem varAlFinal_compact_sequence
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B C₀ : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α : ℝ)
    (hη : 0 < η) (hB : 0 < B) (hC₀ : 0 < C₀)
    (hα : P.val.2 - 1 < α) (hα2 : α < P.val.2 / 2)
    (ell : Scales)
    (hell : Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0))
    (hreg : ∀ N : ℕ+,
      PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
      TransportRegularity P (observationLength (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
          n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (h : ℝ),
      1 ≤ (N : ℝ) * (ell N).val → ((N : ℝ) * (ell N).val)⁻¹ ≤ h → h ≤ 1 →
      ∀ ψ : {g : Circle (observationLength (ell N)) → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength (observationLength (ell N)))},
        (∀ k, coeff (observationLength (ell N)) ⟨(fun x => (ψ.val x : ℂ)),
          complexL2Integrable _ _ ψ.property⟩ k =
            transportCoeffs P (observationLength (ell N))
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k) →
        ∃ hi : Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
            (loopScaleField (ell N).val (circleMollify ρ (ell N).val⁻¹ h
              (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))))) X.val)
            (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal
            (C * ((N : ℝ) * (ell N).val) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  obtain ⟨m, A, hA, hpieces⟩ := varAl_pieces_compact_complete P hPL p hp η B C₀ n marks α
    hη hB hC₀ hα hα2 ell hell hreg ρ hρ
  obtain ⟨C, hC, hv⟩ := varAlFinal_finite_pieces hBE hPL P m hα.le hα2 hA hε
  refine ⟨C, hC, fun N h hK hh hh1 ψ hcoeff => ?_⟩
  obtain ⟨φ, hφ, hsum, henv, _, _⟩ := hpieces N h hK hh hh1 ψ hcoeff
  exact hv N (ell N).val _ φ (ell N).property.1 (ell N).property.2 hK
    (fun j => ⟨(hφ j).1, (hφ j).2.1⟩) hsum henv

end Riesz1.Internal

end
