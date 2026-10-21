/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.CompactDecompositionProfile
public import Riesz1.Variance.VarAlFinalMacro

/-!
# Loop variance for the original compact profile

Proposition 5.9, with the coefficient before the scale sequence,
including the endpoint exponent and every particle count and radius.
-/

public section

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace Riesz1

/-- Proposition 5.9, compact branch, with the coefficient before the scale
sequence. The only external premises are `External.BakryEmery` and
`External.PrekopaLeindler`. -/
theorem varAl_loop_variance_compact
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (hp : CompactProfile p) (α : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      ∀ (N : ℕ+) (h : ℝ), 1 ≤ (N : ℝ) * (ell N).val →
        ((N : ℝ) * (ell N).val)⁻¹ ≤ h → h ≤ 1 →
        ∀ ψ : {g : Circle (observationLength (ell N)) → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength (observationLength (ell N)))},
          (∀ k, coeff (observationLength (ell N)) ⟨(fun x => (ψ.val x : ℂ)),
            complexL2Integrable _ _ ψ.property⟩ k = transportCoeffs P (observationLength (ell N))
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k) →
          ∃ hi : Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
              (loopScaleField (ell N).val (circleMollify ρ (ell N).val⁻¹ h
                (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))))) X.val)
              (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal
              (C * ((N : ℝ) * (ell N).val) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  obtain ⟨α', hα', hα'2, hαα', hpower⟩ :=
    Internal.varAlFinal_interior_exponent P.property.2.2 hα hα2
  obtain ⟨E, hE, hpieces⟩ := Internal.compactDecomposition_profile P p hp d.1 d.2.1 d.2.2.1
    d.2.2.2.1 d.2.2.2.2 α α' hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  obtain ⟨C, hC, hv⟩ := Internal.varAlFinal_finite_pieces hBE hPL P
    ((d.2.2.2.1 : ℕ) + 1) hα'.le hα'2 hE hε
  refine ⟨C, hC, fun ell hell hreg N h hK hh hh1 ψ hf => ?_⟩
  obtain ⟨φ, hφ, hsum, henv⟩ := hpieces ell hell hreg N h hK hh hh1 ψ hf
  have htrans (j : Fin ((d.2.2.2.1 : ℕ) + 1)) : ∃ a : ℝ,
      (∀ x, |deriv (fun t => φ j (t + a)) x| ≤ E *
        gradWeightOne P.val.2 (1 - P.val.2 + α') ((N : ℝ) * (ell N).val) (ell N).val⁻¹ x) ∧
      (∀ x, |deriv (deriv (fun t => φ j (t + a))) x| ≤ E *
        gradWeightTwo P.val.2 (1 - P.val.2 + α') ((N : ℝ) * (ell N).val) (ell N).val⁻¹ x) := by
    let a : ℝ := Fin.lastCases 0 d.2.2.2.2 j
    refine ⟨a, fun x => ?_, fun x => ?_⟩
    · rw [deriv_comp_add_const]
      simpa only [a, add_sub_cancel_right] using (henv j (x + a)).1
    · rw [show deriv (fun t => φ j (t + a)) = fun t => deriv (φ j) (t + a) from
        funext fun t => deriv_comp_add_const (φ j) a t, deriv_comp_add_const]
      simpa only [a, add_sub_cancel_right] using (henv j (x + a)).2
  obtain ⟨hi, hb⟩ := hv N (ell N).val _ φ (ell N).property.1 (ell N).property.2
    hK hφ hsum htrans
  exact ⟨hi, by rwa [hpower] at hb⟩

end Riesz1
