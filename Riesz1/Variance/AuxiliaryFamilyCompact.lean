/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryFamilyCompactBounds
public import Riesz1.Variance.AuxiliaryFamilyEnergyEnvelope
public import Riesz1.Variance.AuxiliaryFamilyDerivativeEnvelope
public import Riesz1.Variance.AuxiliaryFamilyRates
public import Riesz1.Variance.AuxiliaryReductionIdentity
import all Riesz1.Variance.LoopMaster

/-!
# Both auxiliary family estimates for compact profiles

Proposition 5.6, with the full `OptimalScalingTest` family
domain, including the endpoint exponent.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace Riesz1.Internal

/-- Sharp derivative variance and energy for all compact family tests,
from `External.BakryEmery` and `External.PrekopaLeindler` only. -/
theorem auxiliary_family_compact_estimates
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (hp : CompactProfile p) (α : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (nhds 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) → ∀ r : ℝ, 0 < r →
      ∀ (v : Profile) (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
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
  let b := 1 - P.val.2 + (α + δ)
  have hb : 0 ≤ b := by dsimp [b]; linarith
  obtain ⟨A, hA, hbound⟩ := auxiliary_family_compact_transport_bounds P p hp α (α + δ) d
    hα hα2 (by linarith) hα'0 hα'2 hη hB hC₀ ρ hρ
  obtain ⟨V, hV, hv⟩ := auxiliary_family_derivative_envelopes hBE hPL P
    (d.2.2.2.1 : ℕ) d.2.2.2.2 b (ε / 2) hb (by linarith)
  obtain ⟨D, hD, hj⟩ := auxiliary_family_transport_energy_envelopes
    (d.2.2.2.1 : ℕ) d.2.2.2.2 P.property.2.2 hb (show 0 < ε / 2 by linarith)
  let C := (V + D + 1) * A ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hVC : V * A ^ 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg A]
  have hDC : D * A ^ 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg A]
  refine ⟨C, hC, fun ell hell hdata N hK r hr v f hf ψ hψ htr => ?_⟩
  dsimp only
  let a := ell N
  let Ψ := loopMasterProfile a ψ hψ
  have hΨ : ContDiff ℝ ∞ Ψ.val := hψ
  have hpΨ : Function.Periodic Ψ.val a.val⁻¹ := Ψ.property.1
  have hq := (contDiff_infty_iff_deriv.mp hΨ).2
  have hpq := Riesz1.periodic_deriv hpΨ
  have hh : 0 < (cltK N a)⁻¹ := inv_pos.mpr (cltK_pos N a)
  obtain ⟨h1, h2, ht⟩ := hbound ell hell hdata N hK r hr v f hf ψ hψ htr
  obtain ⟨hi, hvar⟩ := hv N a hK (cltK N a)⁻¹ A hh le_rfl hA.le
    (deriv Ψ.val) hq hpq h1 h2 ht
  have henergy := hj a.val (cltK N a) (cltK N a)⁻¹ A a.property.1 hK hh le_rfl hA.le
    Ψ.val hΨ hpΨ h1 (fun x hx => (ht x hx).1)
  have hrates := auxiliary_family_increased_rates (s := P.val.2) (α := α)
    hK (by linarith : 2 * δ ≤ ε / 2) hε.le
  constructor
  · have hmem := auxiliary_derivative_stat_memLp P N a Ψ hΨ
    refine ⟨hmem, hvar.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    calc
      _ ≤ C * (cltK N a ^ (ε / 2) *
          (cltK N a ^ P.val.2 + cltK N a ^ (2 * b))) :=
        mul_le_mul_of_nonneg_right hVC (by positivity)
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrates.1 hC.le
  · exact henergy.trans ((mul_le_mul_of_nonneg_right hDC (by positivity)).trans
      (mul_le_mul_of_nonneg_left hrates.2 hC.le))

end Riesz1.Internal

end
