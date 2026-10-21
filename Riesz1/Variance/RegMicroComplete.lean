/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroCompleteCompact
public import Riesz1.Variance.RegMicroCompleteMacroscopic
public import Riesz1.Variance.AuxiliaryVarianceInput

/-!
# Microscopic regularization variance

Every assertion of Lemma 5.3, with the Bakry–Émery criterion `External.BakryEmery`
and the Prékopa–Leindler inequality `External.PrekopaLeindler` as hypotheses.
The coefficient is chosen after the fixed profile and its data,
before the scale sequence and particle number. No marked separation is assumed.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace Riesz1

/-- Lemma 5.3, including all exponent cases, bounded
`K` and `N=1`, with the constant before the scale sequence. -/
theorem reg_micro
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) →
        let ξ := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
          {f : Circle (loopMasterLength (ell N)) → ℝ //
            MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
        ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ))) 2
          (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
            ENNReal.ofReal (C*cltK N (ell N)^ε*
              (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
  classical
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d
  · obtain ⟨ell₀, h₀⟩ := hex
    rcases h₀ with ⟨hα0, hα1, hη, _hηs, hB, hC₀, _hcases⟩
    have hcompact : ∃ D : ℝ, 0 < D ∧ ∀ ell : Scales, CompactProfile p →
        Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
              d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
        ∀ N : ℕ+, 1 ≤ cltK N (ell N) →
          let ξ := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
            {f : Circle (loopMasterLength (ell N)) → ℝ //
              MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
          ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ))) 2
            (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
              ENNReal.ofReal (D*cltK N (ell N)^ε*
                (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
      by_cases hp : CompactProfile p
      · obtain ⟨D, hD, hb⟩ := reg_micro_compact hBE hPL P p hp α d.1 d.2.1 d.2.2.1
          d.2.2.2.1 d.2.2.2.2 hα0 hα1 hη hB.le hC₀.le ρ hρ ε hε
        exact ⟨D, hD, fun ell _ => hb ell⟩
      · exact ⟨1, zero_lt_one, fun _ hp' => False.elim (hp hp')⟩
    have hmacro : ∃ D : ℝ, 0 < D ∧ ∀ ell : Scales, (∀ N, (ell N).val = 1) →
        PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ →
        TransportRegularity P unitLength ⟨p.val, p.property⟩
          d.2.2.2.1 d.2.2.2.2 α d.2.2.1 →
        ∀ N : ℕ+, 1 ≤ cltK N (ell N) →
          let ξ := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
            {f : Circle (loopMasterLength (ell N)) → ℝ //
              MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
          ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 ξ (mixedReg hρ N (ell N) ξ))) 2
            (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
              ENNReal.ofReal (D*cltK N (ell N)^ε*
                (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
      by_cases hm : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
          TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1
      · obtain ⟨D, hD, hb⟩ := reg_micro_macroscopic hBE hPL P p α d.1 d.2.1 d.2.2.1
          d.2.2.2.1 d.2.2.2.2 hα0 hα1 hη hB.le hC₀.le hm.1 hm.2 ρ hρ ε hε
        exact ⟨D, hD, fun ell hell _ _ => hb ell hell⟩
      · exact ⟨1, zero_lt_one, fun _ _ hp ht => False.elim (hm ⟨hp, ht⟩)⟩
    obtain ⟨Dc, hDc, hc⟩ := hcompact
    obtain ⟨Dm, hDm, hm⟩ := hmacro
    refine ⟨Dc+Dm, add_pos hDc hDm, fun ell hadm N hK => ?_⟩
    have hrate : 0 ≤ cltK N (ell N)^ε*
        (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2)) := by positivity
    rcases hadm.2.2.2.2.2.2 with hmac | hcomp
    · obtain ⟨hE, hv⟩ := hm ell hmac.1 hmac.2.1 hmac.2.2 N hK
      refine ⟨hE, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      nlinarith [mul_nonneg hDc.le hrate]
    · obtain ⟨hE, hv⟩ := hc ell hcomp.1 hcomp.2.1 hcomp.2.2 N hK
      refine ⟨hE, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      nlinarith [mul_nonneg hDm.le hrate]
  · exact ⟨1, zero_lt_one, fun ell hadm => False.elim (hex ⟨ell, hadm⟩)⟩

end Riesz1

namespace Riesz1.Internal

/-- The microscopic input consumed by the original-profile auxiliary
variance reduction, discharged using only the Bakry–Émery criterion and
the Prékopa–Leindler inequality as hypotheses. -/
theorem auxiliaryMicroVarianceInput_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) :
    AuxiliaryMicroVarianceInput :=
  reg_micro hBE hPL

end Riesz1.Internal
