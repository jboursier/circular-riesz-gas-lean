/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroMarksComplete
public import Riesz1.Variance.RegMicroUniformSeparated

/-!
# Microscopic variance for every fixed compact profile

Lemma 5.3, with no separation assumption. The coefficient
is chosen after the fixed profile and before the scale sequence. The
assembly includes both exceptional exponents, bounded `K` and `N=1`.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace Riesz1

/-- The complete compact regime of microscopic regularization variance,
with the constant chosen before the scale sequence and no restriction on the exterior real marks. -/
theorem reg_micro_compact
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (α η B C₀ : ℝ) (n : ℕ+) (a : Fin (n : ℕ) → ℝ)
    (hα0 : P.val.2-1 ≤ α) (hα1 : α < P.val.2/2)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n a α C₀) →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) →
        let f := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
          {f : Circle (loopMasterLength (ell N)) → ℝ //
            MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
        ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
          (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
            ENNReal.ofReal (D*cltK N (ell N)^ε*
              (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
  obtain ⟨m, b, C, δ, hC, hδ, hsep, hreg⟩ := Internal.regMicro_compact_marks
    P p hp η B C₀ α n a hη hB hC₀ hα0 hα1
  obtain ⟨D, hD, hbound⟩ := Internal.regMicro_compact_of_uniform_separation
    hBE hPL P p hp α η B C m b hα0 hα1 hη hB hC.le δ hδ
    (fun c _ => hsep c.val⁻¹ ((one_le_inv₀ c.property.1).mpr c.property.2)) ρ hρ ε hε
  exact ⟨D, hD, fun ell hell hfamily => hbound ell hell
    (fun N => ⟨(hfamily N).1, hreg ell hell hfamily (ell N) (hfamily N).1⟩)⟩

end Riesz1
