/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.MainConclusions
public import Riesz1.Bridges.PowerVariance
public import Riesz1.Bridges.FluctuationSquare
public import Riesz1.Kernel.AdmissibleExamplesPositive
public import Riesz1.Gibbs.WellDefined
public import Riesz1.Frozen.PowerExponent
public import Riesz1.Frozen.PowerRieszExponent
public import Riesz1.Frozen.PowerVariance
public import Riesz1.Frozen.RieszRepresentative
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.Fluctuation

/-!
# The power-law observable from the CLT conclusion

Corollary 2. The CLT conclusion of Theorem 3 is an explicit hypothesis. The scale is identically
one, the profile is the Riesz representative `g_α`, and the exponent is `α`. The `L²` membership,
zero mean, positive variance and the identification of the limiting variance are proved here
unconditionally.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

namespace Internal

/-- Corollary 2, with the CLT conclusion `CLTConclusion` as an explicit hypothesis. The
statement is the body of `Riesz1.power_law_observable` after its binder
`∀ beta s hbeta hs hs1`. -/
theorem power_law_observable_of_variance_clt (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1) (hCLT : CLTConclusion beta s hbeta hs hs1) :
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ∀ (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < s / 2),
      let a : PowerExponent P := ⟨alpha, ha, ha1⟩
      ModelWellDefined P ∧
      MemLp (fun x => (rieszRepresentative (powerRieszExponent P a) x : ℂ)) 2 volume ∧
      ∃ hf : Integrable (rieszRepresentative (powerRieszExponent P a)) volume,
      (∫ x : UnitAddCircle, rieszRepresentative (powerRieszExponent P a) x) = 0 ∧
      0 < powerVariance P a ∧
      (∀ N : ℕ+,
        AEMeasurable (fun X : Configuration N => (N : ℝ) ^ (-s / 2) *
          fluctuation ⟨rieszRepresentative (powerRieszExponent P a), hf⟩ X) (gibbsMeasure P N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure P (particleNumber n)).map
          (fun X => (particleNumber n : ℝ) ^ (-s / 2) *
            fluctuation ⟨rieszRepresentative (powerRieszExponent P a), hf⟩ X))
        (normalLaw (Real.toNNReal (powerVariance P a))) := by
  intro P alpha ha ha1 a
  obtain ⟨hMem, hmean, hform⟩ := explicit_formulas_power_powerVariance P a
  have hf : Integrable (rieszRepresentative (powerRieszExponent P a)) volume := by
    simpa using hMem.re.integrable one_le_two
  -- The profile of the CLT and its admissibility at scale one.
  let p : Profile := ⟨rieszRepresentative (powerRieszExponent P a), hMem⟩
  let ell : Scales := fun _ => ⟨1, zero_lt_one, le_rfl⟩
  obtain ⟨_, d, hadm⟩ := admissible_riesz P (powerRieszExponent P a) ha1
  have hmeso : Mesoscopic ell := by
    unfold Mesoscopic
    simp only [ell, mul_one]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hconv := ((hCLT p alpha d).1 ell hadm hmeso).2.2.1 (fun _ => rfl)
  -- At scale one the test profile is the profile itself.
  have htas : ∀ N : ℕ+, testAtScale p (ell N) = rieszRepresentative (powerRieszExponent P a) := by
    intro N
    unfold testAtScale
    simp [ell, p]
  -- The statistic at scale one is the power-law fluctuation.
  have hlaw : statisticLaws P p ell = fun n => (gibbsMeasure P (particleNumber n)).map
      (fun X => (particleNumber n : ℝ) ^ (-s / 2) *
        fluctuation ⟨rieszRepresentative (powerRieszExponent P a), hf⟩ X) := by
    funext n
    unfold statisticLaws normalizedStatistic
    congr 1
    funext X
    have hsub : (⟨testAtScale p (ell (particleNumber n)), testAtScaleL1 p (ell (particleNumber n))⟩ :
        {f : UnitAddCircle → ℝ // Integrable f volume}) =
          ⟨rieszRepresentative (powerRieszExponent P a), hf⟩ :=
      Subtype.ext (htas (particleNumber n))
    rw [hsub]
    simp only [ell, mul_one]
    rfl
  -- The limiting variance at scale one is the power-law variance. The profile at scale one is
  -- the Riesz representative, so the circle seminorm is that of `hMem`.
  have htas1 : testAtScale p ⟨1, zero_lt_one, le_rfl⟩ = rieszRepresentative (powerRieszExponent P a) :=
    htas 1
  have hcirc : circleVariance P p ⟨1, zero_lt_one, le_rfl⟩ =
      ENNReal.ofReal (powerVariance P a) := by
    obtain ⟨hS, hval⟩ := hform hMem
    have hK : 0 ≤ (2 * Real.pi) ^ (1 - P.val.2) /
        (2 * P.val.1 * rieszConstant (parametersExponent P)) := by
      have := rieszConstant_pos (parametersExponent P)
      have := P.property.1
      positivity
    have hsub1 : (⟨fun x => (testAtScale p ⟨1, zero_lt_one, le_rfl⟩ x : ℂ),
        testAtScaleL2 p ⟨1, zero_lt_one, le_rfl⟩⟩ : {g : UnitAddCircle → ℂ // MemLp g 2 volume}) =
          ⟨fun x => (rieszRepresentative (powerRieszExponent P a) x : ℂ), hMem⟩ :=
      Subtype.ext (by simp only [htas1])
    unfold circleVariance
    rw [hsub1]
    simp only [Real.one_rpow, mul_one]
    rw [← hval, ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hS]
  have hlim : normalLaw (circleVariance P p ⟨1, zero_lt_one, le_rfl⟩).toNNReal =
      normalLaw (Real.toNNReal (powerVariance P a)) := by
    rw [hcirc]
    rfl
  rw [hlaw, hlim] at hconv
  refine ⟨modelWellDefined P, hMem, ⟨hf, hmean, powerVariance_pos P a, ?_, hconv⟩⟩
  intro N
  have hfR : MemLp (rieszRepresentative (powerRieszExponent P a)) 2 volume := by
    simpa using hMem.re
  exact ((memLp_fluctuation P N hfR).aemeasurable).const_mul _

end Internal

end Riesz1

end
end
