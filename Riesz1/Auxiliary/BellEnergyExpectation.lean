/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellEnergyPairs
public import Riesz1.Auxiliary.BellEnergyBackground

/-!
# The expectation identity for the quadratic energy

The four absolutely integrable terms combine into
`N Σ E q(Sₖ) - N ∫ q`, as in the splitting identity of Lemma B.1.
The identity includes the single-particle case and needs no rigidity.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The splitting identity of Lemma B.1, including `N = 1`. -/
theorem bell_quadratic_loop_expectation (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) :
    (∫ X : Configuration N, bellQuadraticLoop (parametersExponent P) N ℓ ψ X
      ∂gibbsMeasure P N) =
      (N : ℝ) * (∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1),
        ∫ X : Configuration N, bellKernel P.1.2 N ℓ.val ψ.val (blockLength X 0 k)
          ∂gibbsMeasure P N) -
      (N : ℝ) * ∫ y in (0 : ℝ)..(N : ℝ), bellKernel P.1.2 N ℓ.val ψ.val y := by
  have := (modelWellDefined P N).2.2
  let s := parametersExponent P
  let f := loopScaleField ℓ.val ψ.val
  let B := ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, bellPairKernel P.1.2 f x y
  let T := fun X : Configuration N =>
    ∑ p ∈ (Finset.univ : Finset (Fin (N : ℕ))).offDiag,
      bellPairKernel P.1.2 f (X.val p.1) (X.val p.2)
  let U := fun X : Configuration N =>
    ∑ i : Fin (N : ℕ), ∫ y in (0 : ℝ)..1, bellPairKernel P.1.2 f (X.val i) y
  obtain ⟨M, hf⟩ := loopScaleField_lipschitz ψ
  have hp : Function.Periodic f 1 := loopScaleField_periodic ψ.2.1
  have hiT : Integrable T (gibbsMeasure P N) :=
    integrable_finsetSum _ fun p hp' =>
      bellPair_particle_integrable P hPL N hf hp p.1 p.2 (Finset.mem_offDiag.mp hp').2.2
  have hiU (i : Fin (N : ℕ)) : Integrable (fun X : Configuration N =>
      ∫ y in (0 : ℝ)..1, bellPairKernel P.1.2 f (X.val i) y) (gibbsMeasure P N) :=
    bellPair_background_comp_integrable (gibbsMeasure P N) s hf hp
      ((measurable_pi_apply i).comp measurable_subtype_coe)
  have hiUs : Integrable U (gibbsMeasure P N) :=
    integrable_finsetSum _ fun i _ => hiU i
  have hU : (∫ X : Configuration N, U X ∂gibbsMeasure P N) = (N : ℝ) * B := by
    rw [show U = (fun X : Configuration N =>
      ∑ i : Fin (N : ℕ), ∫ y in (0 : ℝ)..1, bellPairKernel P.1.2 f (X.val i) y) from rfl,
      integral_finsetSum _ (fun i _ => hiU i)]
    simp_rw [integral_bell_particle_background (f := f) P N hf.continuous hp]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, B]
  have hT : (N : ℝ) ^ (-P.1.2) * (∫ X : Configuration N, T X ∂gibbsMeasure P N) =
      (N : ℝ) * ∑ k ∈ Finset.Icc 1 ((N : ℕ) - 1),
        ∫ X : Configuration N, bellKernel P.1.2 N ℓ.val ψ.val (blockLength X 0 k)
          ∂gibbsMeasure P N := by
    rw [← integral_const_mul]
    exact integral_bell_particle_sum_all P hPL N ℓ ψ hψ
  have hB : (N : ℝ) ^ (-P.1.2) * B =
      (N : ℝ)⁻¹ * ∫ y in (0 : ℝ)..(N : ℝ), bellKernel P.1.2 N ℓ.val ψ.val y :=
    bell_background_eq_integral_kernel s N ℓ ψ
  have he (X : Configuration N) : bellQuadraticLoop s N ℓ ψ X =
      (N : ℝ) ^ (-P.1.2) * (T X - (2 * (N : ℝ)) * U X + (N : ℝ) ^ 2 * B) := by
    have hsym : (∑ j : Fin (N : ℕ), ∫ x in (0 : ℝ)..1,
        bellPairKernel P.1.2 f x (X.val j)) = U X := by
      apply Finset.sum_congr rfl
      intro j _
      exact intervalIntegral.integral_congr fun x _ => bellPairKernel_symm _ _ _ _
    dsimp only [bellQuadraticLoop, s, parametersExponent]
    change (N : ℝ) ^ (-P.1.2) * (T X - (N : ℝ) * U X - (N : ℝ) * _ + (N : ℝ) ^ 2 * B) = _
    rw [hsym]
    ring
  change (∫ X : Configuration N, bellQuadraticLoop s N ℓ ψ X ∂gibbsMeasure P N) = _
  simp_rw [he]
  rw [integral_const_mul,
    integral_add (f := fun X : Configuration N => T X - (2 * (N : ℝ)) * U X)
      (g := fun _ : Configuration N => (N : ℝ) ^ 2 * B)
      (hiT.sub (hiUs.const_mul _)) (integrable_const _),
    integral_sub (f := T) (g := fun X : Configuration N => (2 * (N : ℝ)) * U X)
      hiT (hiUs.const_mul _), integral_const_mul, integral_const, hU]
  simp only [probReal_univ, one_smul]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  calc
    _ = (N : ℝ) ^ (-P.1.2) * (∫ X : Configuration N, T X ∂gibbsMeasure P N) -
        (N : ℝ) ^ 2 * ((N : ℝ) ^ (-P.1.2) * B) := by ring
    _ = _ := by rw [hT, hB]; field_simp [hN]

end Riesz1

end
