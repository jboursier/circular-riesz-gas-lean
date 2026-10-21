/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryFamilyMacroBounds
public import Riesz1.Variance.AuxiliaryFamilyMacroEnvelope
public import Riesz1.Variance.AuxiliaryFamilyRates
import all Riesz1.Variance.LoopMaster

/-!
# The two auxiliary family estimates at macroscopic scales

Proposition 5.6, uniform over all three branches of
`OptimalScalingTest`, including the endpoint exponent.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- Derivative variance and energy for the actual macroscopic family
transports. All fixed profile hypotheses precede the coefficient.
All scales, particle counts and family radii follow it. -/
theorem auxiliary_family_macro_estimates
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (hprim : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : Scales) (N : ℕ+), (ell N).val = 1 →
      ∀ (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N)) ⟨(fun x => (ψ x : ℂ)),
            complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N)) (mixedReg hρ N (ell N) f) k) →
          let Q := fun X : Configuration N =>
            fluctIntegral (fun u => deriv (loopMasterProfile (ell N) ψ hψ).val
              (u / (ell N).val)) N X.val
          (∃ hQ : MemLp Q 2 (gibbsMeasure P N),
            variance (gibbsMeasure P N) Q (hQ.integrable one_le_two) ≤
              ENNReal.ofReal (C * cltK N (ell N) ^ ε *
                (cltK N (ell N) ^ P.val.2 +
                  cltK N (ell N) ^ (2 * (1 - P.val.2 + α))))) ∧
          bellEnergy (ell N).val (loopMasterProfile (ell N) ψ hψ).val ≤
            C * (cltK N (ell N) ^ ε *
              (1 + cltK N (ell N) ^ (2 * (1 - P.val.2 + α) - 1))) := by
  obtain ⟨δ, hδ, hα'0, hα'2, _, hδε⟩ := reg_micro_endpoint_choice hα hα2 hε
  obtain ⟨A, hA, hbound⟩ := auxiliary_family_macro_transport_bounds P p α (α + δ) d
    hα hα2 (by linarith) hα'0 hα'2 hη hB hC₀ hprim hreg ρ hρ
  obtain ⟨C, hC, hest⟩ := auxiliary_family_macro_envelopes hBE hPL P
    (d.2.2.2.1 : ℕ) d.2.2.2.2 hreg.1 (b := 1 - P.val.2 + (α + δ))
    (S := A) (A := A) (ε := ε / 2) (by linarith) hA.le hA.le (by linarith)
  refine ⟨C, hC, fun ell N ha r v f hv ψ hψ htr => ?_⟩
  dsimp only
  let F := fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N)))
  have hp : Function.Periodic F 1 := by
    have hl : (loopMasterLength (ell N)).val = 1 := by
      change (ell N).val⁻¹ = 1; rw [ha, inv_one]
    rw [← hl]
    intro x
    simp only [F, AddCircle.coe_add_period]
  have hb := hbound ell N ha r v f hv ψ hψ htr
  obtain ⟨hvar, henergy⟩ := hest N (N : ℝ)⁻¹ le_rfl F hψ hp
    (fun x => (hb x).1) (fun x => (hb x).2.1) (fun x => (hb x).2.2)
  have hK : cltK N (ell N) = (N : ℝ) := by
    change (N : ℝ) * (ell N).val = _; rw [ha, mul_one]
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ (N : ℕ) from N.pos)
  have hrates := auxiliary_family_increased_rates (s := P.val.2) (α := α)
    hN (by linarith : 2 * δ ≤ ε / 2) hε.le
  have hQeq : (fun X : Configuration N =>
      fluctIntegral (fun u => deriv (loopMasterProfile (ell N) ψ hψ).val
        (u / (ell N).val)) N X.val) = fun X => fluctIntegral (deriv F) N X.val := by
    simp only [ha, div_one, F]
  rw [hQeq, hK]
  constructor
  · obtain ⟨hQ, hV⟩ := hvar
    exact ⟨hQ, hV.trans (ENNReal.ofReal_le_ofReal (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrates.1 hC.le))⟩
  · change bellEnergy (ell N).val F ≤ _
    rw [ha]
    exact henergy.trans (mul_le_mul_of_nonneg_left hrates.2 hC.le)

end Riesz1.Internal

end
