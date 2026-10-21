/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryFamilyMacro

/-!
# The macroscopic branches of the auxiliary family inputs

The estimates of Proposition 5.6 and the family uniformity of Theorem 2, with exactly the
admissibility hypotheses of the paper. The constant is chosen before the scale sequence and
the particle number.
-/

public section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- Both requested auxiliary estimates on the macroscopic branch, from
the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler` only. The family radius is unrestricted except
by the existing test relation. -/
theorem auxiliary_family_macroscopic_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : Scales), Admissible P p ell α d →
      (∀ M, (ell M).val = 1) → ∀ (N : ℕ+),
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
  classical
  let H := ∃ ell : Scales, Admissible P p ell α d ∧ ∀ M, (ell M).val = 1
  by_cases hex : H
  · obtain ⟨ell₀, hadm, hone⟩ := hex
    obtain ⟨hα, hα2, hη, _, hB, hC₀, hcases⟩ := hadm
    have hdata : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
        TransportRegularity P unitLength ⟨p.val, p.property⟩
          d.2.2.2.1 d.2.2.2.2 α d.2.2.1 := by
      rcases hcases with ⟨_, hprim, hreg⟩ | ⟨_, hlim, _⟩
      · exact ⟨hprim, hreg⟩
      · have hc : Filter.Tendsto
            (fun k : ℕ => (ell₀ ⟨k + 1, Nat.succ_pos k⟩).val)
            Filter.atTop (nhds (1 : ℝ)) := by
          have heq : (fun k : ℕ => (ell₀ ⟨k + 1, Nat.succ_pos k⟩).val) =
              fun _ : ℕ => (1 : ℝ) := funext (fun k => hone _)
          rw [heq]
          exact tendsto_const_nhds
        have hh := tendsto_nhds_unique hc hlim
        norm_num at hh
    obtain ⟨C, hC, hall⟩ := auxiliary_family_macro_estimates hBE hPL P p α d hα hα2
      hη hB.le hC₀.le hdata.1 hdata.2 ρ hρ ε hε
    exact ⟨C, hC, fun ell _ hell N => hall ell N (hell N)⟩
  · refine ⟨1, one_pos, fun ell hadm hone => ?_⟩
    exact False.elim (hex ⟨ell, hadm, hone⟩)

end Riesz1.Internal

end
