/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroLargeFamilies
public import Riesz1.Variance.RegMicroUniformSeparated

/-!
# Uniform compact microscopic variance for both families

Lemma 5.3 in the compact regime, uniformly over both
families. The sole additional geometric hypothesis is
the original-profile uniform separation.
It is confined to this internal helper. Gibbs Fourier comparison means
that the family members require no new separated marked sets.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz1.Internal

/-- Compact microscopic variance with a common coefficient for the
original test and both families, conditional only on separation for the
original transport. The assertion includes every `K≥1`, not just large `K`. -/
theorem regMicroFamily_compact_of_uniform_separation
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (α η B C₀ : ℝ) (n : ℕ+) (a : Fin (n : ℕ) → ℝ)
    (hα0 : P.val.2-1 ≤ α) (hα1 : α < P.val.2/2)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ (b : Scale),
      TransportRegularity P (observationLength b)
        ⟨periodizedProfile p (observationLength b), periodizedProfileL2 p b⟩ n a α C₀ →
      ∀ i j, i ≠ j → δ ≤ dist (a i : Circle (observationLength b))
        (a j : Circle (observationLength b)))
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ell : Scales),
      Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
          n a α C₀) →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) → ∀ (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
            (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
            ENNReal.ofReal (D*cltK N (ell N)^ε*
              (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
  obtain ⟨D, hD, hb⟩ := regMicro_compact_of_uniform_separation hBE hPL P p hp
    α η B C₀ n a hα0 hα1 hη hB hC₀ δ hδ hsep ρ hρ ε hε
  refine ⟨4*D, by positivity, fun ell hell hreg N hK r v f hv => ?_⟩
  obtain ⟨hξ, hξb⟩ := hb ell hell hreg N hK
  obtain ⟨hE, he⟩ := regMicroFamily_bound_of_original P p ell N hρ r v f hv _
    (hξ.integrable one_le_two) hξb
  refine ⟨hE, ?_⟩
  simpa only [mul_assoc] using he

end Riesz1.Internal
