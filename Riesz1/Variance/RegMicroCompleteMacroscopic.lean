/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFinalFixed
public import Riesz1.CLT.ErrorOneTransfer

/-!
# Macroscopic microscopic variance with the quantifier order of the paper

The periodized test differs from the base representative at an antipode.
Fourier coefficient identities transfer both regularity predicates
before the fixed-circle theorem is applied.
-/

public section

open MeasureTheory

namespace Riesz1

/-- Lemma 5.3 for all macroscopic scale sequences,
with one coefficient before the sequence and particle number. -/
theorem reg_micro_macroscopic
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α η B C₀ : ℝ)
    (n : ℕ+) (a : Fin (n : ℕ) → ℝ)
    (hα0 : P.val.2-1 ≤ α) (hα1 : α < P.val.2/2)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n a α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ ell : Scales, (∀ N, (ell N).val = 1) →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) →
        let f := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
          {f : Circle (loopMasterLength (ell N)) → ℝ //
            MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
        ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
          (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
            ENNReal.ofReal (D*cltK N (ell N)^ε*
              (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
  let b : Scale := ⟨1, by norm_num⟩
  let ξ := (⟨periodizedProfile p (observationLength b), periodizedProfileL2 p b⟩ :
    {f : Circle (observationLength b) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (observationLength b))})
  have htransfer (L : Length) (hL : L.val = 1)
      (hf : MemLp (fun z => (periodizedProfile p L z : ℂ)) 2 (arclength L)) :
      PrimitiveRegularity L η P.val.2 B ⟨periodizedProfile p L, hf⟩ ∧
        TransportRegularity P L ⟨periodizedProfile p L, hf⟩ n a α C₀ := by
    rcases L with ⟨v, hv⟩
    change v = 1 at hL
    subst v
    obtain ⟨Ξ, hΞ, hΞc⟩ := hprim
    rcases hreg with ⟨hinj, ψ, hψ, hpoint⟩
    refine ⟨⟨Ξ, hΞ, fun k hk => (hΞc k hk).trans
      (Internal.coeff_periodizedProfile_eq_unit p ⟨1, hv⟩ rfl hf k).symm⟩,
      hinj, ψ, fun k => ?_, hpoint⟩
    exact (hψ k).trans (Internal.transportCoeffs_periodizedProfile_eq_unit P p ⟨1, hv⟩ rfl hf k).symm
  obtain ⟨hpb, htb⟩ := htransfer (observationLength b)
    (by simp only [observationLength, b, inv_one]) ξ.property
  obtain ⟨D, hD, hb⟩ := reg_micro_fixed_scale hBE hPL P b α η B C₀ n a
    hα0 hα1 hη hB hC₀ ξ hpb htb ρ hρ ε hε
  refine ⟨D, hD, fun ell hell N hK => ?_⟩
  have heq : ell N = b := Subtype.ext (hell N)
  dsimp only
  rw [heq]
  exact hb N (by simpa only [heq] using hK)

end Riesz1
