/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroLargeFamilies
public import Riesz1.Variance.RegMicroFinalFixed
public import Riesz1.CLT.ErrorOneTransfer

/-!
# Macroscopic microscopic variance for the two families

Lemma 5.3, uniformly over the original test and
both families. The fixed-scale theorem is applied once
to the original profile, before the extra radius is chosen. Fourier
comparison then gives one coefficient for the entire family interval.
-/

public section

open MeasureTheory

namespace Riesz1.Internal

/-- The primitive and transport predicates transfer to the
actual periodized test on any observation circle of length one. -/
theorem regMicro_macroscopic_regularity (P : Parameters) (p : Profile)
    (L : Length) (hL : L.val = 1)
    (hf : MemLp (fun z => (periodizedProfile p L z : ℂ)) 2 (arclength L))
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀) :
    PrimitiveRegularity L η P.val.2 B ⟨periodizedProfile p L, hf⟩ ∧
      TransportRegularity P L ⟨periodizedProfile p L, hf⟩ n marks α C₀ := by
  rcases L with ⟨v, hv⟩
  change v = 1 at hL
  subst v
  obtain ⟨Ξ, hΞ, hΞc⟩ := hprim
  rcases hreg with ⟨hinj, ψ, hψ, hpoint⟩
  refine ⟨⟨Ξ, hΞ, fun k hk => (hΞc k hk).trans
    (coeff_periodizedProfile_eq_unit p ⟨1, hv⟩ rfl hf k).symm⟩,
    hinj, ψ, fun k => ?_, hpoint⟩
  exact (hψ k).trans (transportCoeffs_periodizedProfile_eq_unit P p ⟨1, hv⟩ rfl hf k).symm

/-- The entire macroscopic family estimate, with its coefficient before
the sequence, particle number, and extra radius. No support restriction
on the original profile and no new family admissibility are needed. -/
theorem regMicroFamily_macroscopic
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α η B C₀ : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ)
    (hα0 : P.val.2-1 ≤ α) (hα1 : α < P.val.2/2)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ell : Scales) (N : ℕ+), (ell N).val = 1 →
      1 ≤ cltK N (ell N) → ∀ (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
            (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
            ENNReal.ofReal (D*cltK N (ell N)^ε*
              (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
  let b : Scale := ⟨1, by norm_num⟩
  let ξ := (⟨periodizedProfile p (observationLength b), periodizedProfileL2 p b⟩ :
    {f : Circle (observationLength b) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (observationLength b))})
  obtain ⟨hpb, htb⟩ := regMicro_macroscopic_regularity P p (observationLength b)
    (by simp only [observationLength, b, inv_one]) ξ.property η B n marks α C₀ hprim hreg
  obtain ⟨D, hD, hb⟩ := reg_micro_fixed_scale hBE hPL P b α η B C₀ n marks
    hα0 hα1 hη hB hC₀ ξ hpb htb ρ hρ ε hε
  have original (N : ℕ+) (a : Scale) (ha : a.val = 1) (hK : 1 ≤ cltK N a) :
      let f := (⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ :
        {f : Circle (loopMasterLength a) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))})
      ∃ hE : MemLp (mixedStat P N a (subCircleL2 f (mixedReg hρ N a f))) 2 (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
          ENNReal.ofReal (D*cltK N a^ε*(cltK N a^(2*α)+cltK N a^(3*P.val.2-2))) := by
    have he : a = b := Subtype.ext ha
    subst a
    exact hb N hK
  refine ⟨4*D, by positivity, fun ell N ha hK r v f hv => ?_⟩
  obtain ⟨hξ, hξb⟩ := original N (ell N) ha hK
  obtain ⟨hE, he⟩ := regMicroFamily_bound_of_original P p ell N hρ r v f hv _
    (hξ.integrable one_le_two) hξb
  exact ⟨hE, by simpa only [mul_assoc] using he⟩

end Riesz1.Internal
