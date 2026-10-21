/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellEnergyExpectation
public import Riesz1.Auxiliary.BellRandomSum
public import Riesz1.Variance.LoopMaster

/-!
# The averaged quadratic energy, conditional on rigidity

Lemma B.1, including absolute integrability, for every particle
number. The expectation identity reduces the bound to the random-block
comparison and scalar quadrature. Constants are chosen before the particle
number, scale, profile, and the Prékopa–Leindler inequality `External.PrekopaLeindler`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- Lemma B.1 on the periodic Lipschitz carrier, with a smooth profile. -/
theorem bell_energy_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+)
      (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val),
      1 ≤ (N : ℝ) * ℓ.val → ContDiff ℝ ∞ ψ.val →
      Integrable (bellQuadraticLoop (parametersExponent
        (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)) N ℓ ψ)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      |(∫ X : Configuration N, bellQuadraticLoop (parametersExponent
          (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)) N ℓ ψ X
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)| ≤
          C * (N : ℝ) * ℓ.val * bellEnergy ℓ.val ψ.val := by
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  obtain ⟨Cr, hCr, hr⟩ := bell_random_sum_of_rigidity beta s hbeta hs hs1 hRig
  obtain ⟨Cq, hCq, hq⟩ := bell_quadrature s hs hs1
  refine ⟨Cr + Cq, add_pos hCr hCq, ?_⟩
  intro hPL N ℓ ψ hNℓ hψ
  refine ⟨bell_quadratic_loop_integrable P hPL N ℓ ψ, ?_⟩
  let Q (k : ℕ) := ∫ X : Configuration N,
    bellKernel s N ℓ.val ψ.val (blockLength X 0 k) ∂gibbsMeasure P N
  have hrandom : |(∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), Q k) -
      ∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), bellKernel s N ℓ.val ψ.val (k : ℝ)| ≤
        Cr * bellConstant ℓ.val ψ.val := by
    by_cases hN : 2 ≤ (N : ℕ)
    · obtain ⟨_, hb⟩ := hr hPL N hN ℓ.val ψ.val ℓ.2.1 ℓ.2.2 hNℓ hψ ψ.2.1
      rw [← Finset.sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs _ _).trans hb
    · have hN1 : (N : ℕ) = 1 := by have := N.pos; omega
      simp only [hN1, Nat.sub_self, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
        Finset.sum_empty, sub_self, abs_zero]
      exact mul_nonneg hCr.le (mul_nonneg ℓ.2.1.le (bellEnergy_nonneg ℓ.2.1))
  have hquad := (hq N ℓ.val ψ.val N.pos ℓ.2.1 ℓ.2.2 hNℓ hψ ψ.2.1)
  have hb : |(∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), Q k) -
      ∫ y in (0 : ℝ)..(N : ℝ), bellKernel s N ℓ.val ψ.val y| ≤
        (Cr + Cq) * bellConstant ℓ.val ψ.val := by
    calc _ ≤ |(∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), Q k) -
          ∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), bellKernel s N ℓ.val ψ.val (k : ℝ)| +
        |(∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1), bellKernel s N ℓ.val ψ.val (k : ℝ)) -
          ∫ y in (0 : ℝ)..(N : ℝ), bellKernel s N ℓ.val ψ.val y| := abs_sub_le _ _ _
      _ ≤ _ := by linarith [hrandom, hquad.1.trans hquad.2]
  rw [bell_quadratic_loop_expectation P hPL N ℓ ψ hψ, ← mul_sub, abs_mul,
    abs_of_pos (show (0 : ℝ) < N by exact_mod_cast N.pos)]
  calc _ ≤ (N : ℝ) * ((Cr + Cq) * bellConstant ℓ.val ψ.val) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by unfold bellConstant; ring

/-- **Averaged quadratic energy**, Lemma B.1, for every smooth real periodic
profile. Smooth periodic functions are put on the existing carrier using the proved
Lipschitz certificate. This introduces no additional regularity hypothesis. -/
theorem bell_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+)
      (ℓ : Ioc (0 : ℝ) 1) (ψ : ℝ → ℝ),
      1 ≤ (N : ℝ) * ℓ.val → ∀ (hψ : ContDiff ℝ ∞ ψ)
      (hp : Function.Periodic ψ ℓ.val⁻¹),
      let Ψ : LoopScaleProfile ℓ.val :=
        ⟨ψ, hp, loopMaster_lipschitz (inv_ne_zero ℓ.2.1.ne') hψ hp⟩
      Integrable (bellQuadraticLoop (parametersExponent
        (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)) N ℓ Ψ)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ∧
      |(∫ X : Configuration N, bellQuadraticLoop (parametersExponent
          (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters)) N ℓ Ψ X
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)| ≤
          C * (N : ℝ) * ℓ.val * bellEnergy ℓ.val ψ := by
  obtain ⟨C, hC, h⟩ := bell_energy_of_rigidity beta s hbeta hs hs1 hRig
  exact ⟨C, hC, fun hPL N ℓ ψ hNℓ hψ hp =>
    h hPL N ℓ ⟨ψ, hp, loopMaster_lipschitz (inv_ne_zero ℓ.2.1.ne') hψ hp⟩ hNℓ hψ⟩

end Riesz1.Internal

end
