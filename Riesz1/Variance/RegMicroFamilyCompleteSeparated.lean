/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroLargeMacroscopic
public import Riesz1.Variance.RegMicroLargeSeparated

/-!
# Both admissible regimes with one family coefficient

An internal form of Lemma 5.3, uniform over both
families and all admissible scale sequences. The additional separation
hypothesis is used only in the compact regime. Every constant precedes
the scale sequence and the family radius.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz1.Internal

/-- The full family conclusion on admissible sequences, conditional
on the original-profile separation hypothesis. No separation or
regularity certificate is assumed for the varying family members. -/
theorem regMicroFamily_admissible_of_uniform_separation
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ (b : Scale),
      TransportRegularity P (observationLength b)
        ⟨periodizedProfile p (observationLength b), periodizedProfileL2 p b⟩
          d.2.2.2.1 d.2.2.2.2 α d.2.2.1 →
      ∀ i j, i ≠ j → δ ≤ dist (d.2.2.2.2 i : Circle (observationLength b))
        (d.2.2.2.2 j : Circle (observationLength b)))
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : Scales), Admissible P p ell α d →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) → ∀ (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
            (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
            ENNReal.ofReal (C*cltK N (ell N)^ε*
              (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
  classical
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d
  · obtain ⟨_ell₀, hα0, hα1, hη, _hηs, hB, hC₀, _hcases⟩ := hex
    have hmacro : ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
        PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ →
        TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1 →
        ∀ N : ℕ+, (ell N).val = 1 → 1 ≤ cltK N (ell N) →
        ∀ (r : ℝ) (v : Profile)
          (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
            MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
          OptimalScalingTest p ell N hρ r v f →
          ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
              (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
              ENNReal.ofReal (C*cltK N (ell N)^ε*
                (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
      by_cases hd : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
          TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1
      · obtain ⟨C, hC, hb⟩ := regMicroFamily_macroscopic hBE hPL P p α d.1 d.2.1 d.2.2.1
          d.2.2.2.1 d.2.2.2.2 hα0 hα1 hη hB.le hC₀.le hd.1 hd.2 ρ hρ ε hε
        exact ⟨C, hC, fun ell _ _ => hb ell⟩
      · exact ⟨1, one_pos, fun _ hprim hreg => False.elim (hd ⟨hprim, hreg⟩)⟩
    have hcompact : ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, CompactProfile p →
        Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
              d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
        ∀ N : ℕ+, 1 ≤ cltK N (ell N) → ∀ (r : ℝ) (v : Profile)
          (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
            MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
          OptimalScalingTest p ell N hρ r v f →
          ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
              (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
              ENNReal.ofReal (C*cltK N (ell N)^ε*
                (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
      by_cases hp : CompactProfile p
      · obtain ⟨C, hC, hb⟩ := regMicroFamily_compact_of_uniform_separation hBE hPL P p hp
          α d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 hα0 hα1 hη hB.le hC₀.le
          δ hδ hsep ρ hρ ε hε
        exact ⟨C, hC, fun ell _ => hb ell⟩
      · exact ⟨1, one_pos, fun _ hp' => False.elim (hp hp')⟩
    obtain ⟨Cm, hCm, hm⟩ := hmacro
    obtain ⟨Cc, hCc, hc⟩ := hcompact
    refine ⟨Cm+Cc, add_pos hCm hCc, fun ell hadm N hK r v f hv => ?_⟩
    have hR : 0 ≤ cltK N (ell N)^ε*
        (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2)) := by positivity
    rcases hadm.2.2.2.2.2.2 with ⟨hell, hprim, hreg⟩ | ⟨hp, hell, hfamily⟩
    · obtain ⟨hE, hb⟩ := hm ell hprim hreg N (hell N) hK r v f hv
      refine ⟨hE, hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (by linarith : Cm ≤ Cm+Cc) hR
    · obtain ⟨hE, hb⟩ := hc ell hp hell hfamily N hK r v f hv
      refine ⟨hE, hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (by linarith : Cc ≤ Cm+Cc) hR
  · exact ⟨1, one_pos, fun ell hadm => False.elim (hex ⟨ell, hadm⟩)⟩

end Riesz1.Internal
