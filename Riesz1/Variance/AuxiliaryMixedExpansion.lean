/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryMixedKernel
public import Riesz1.Variance.LoopIBPMoments
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.ToMathlib.PeriodicCircleLift

/-!
# The Gibbs mean of the Hessian pair sum

The Hessian expectation in Proposition 5.6. The Hessian
quadratic term is `β N^{-s}` times the pair sum `∑_{i ≠ j} K_f(x_i, x_j)` of the kernel of
`AuxiliaryMixedKernel`. The fluctuation measure `∑ δ_{x_i} - N dx` expands this pair sum into the
pair term, the two background terms and the double background integral. This file defines the
expansion `hessFluctExpansion` (`∬_{x≠y} · fluct(dx) fluct(dy)` written out) and proves that
the Gibbs mean of the pair sum is `N² ∬ K_f` plus the Gibbs mean of the expansion.

The main results are `Riesz1.integral_hessPairSum_of_integrable` (the identity, given the
integrability of the pair sum) and `Riesz1.integral_hessPairSum` (the integrability is that of the
Hessian quadratic term, from `loop_moments`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology UnitAddCircle

namespace Riesz1

/-- The sum of the Hessian pair kernel over ordered pairs of distinct particles. -/
noncomputable def hessPairSum (s : ℝ) (N : ℕ) (f : ℝ → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, (if j = i then 0 else hessKernel s f (x i) (x j))

/-- The expansion of the Hessian pair sum against the fluctuation measure `∑ δ_{x_i} - N dx`:
the off-diagonal pair term, minus the two background terms, plus the double background
integral. -/
noncomputable def hessFluctExpansion (s : ℝ) (N : ℕ) (f : ℝ → ℝ) (x : Fin N → ℝ) : ℝ :=
  hessPairSum s N f x - 2 * (N : ℝ) * ∑ i : Fin N, hessBackground s f (x i) +
    (N : ℝ) ^ 2 * ∫ u in (0 : ℝ)..1, hessBackground s f u

/-- The Gibbs mean of the Hessian pair sum equals `N²` times the double background integral plus
the Gibbs mean of the fluctuation expansion, for every field `f` that is one-periodic and
Lipschitz and whose pair sum is integrable. -/
theorem integral_hessPairSum_of_integrable (P : Parameters) (N : ℕ+) (s : RieszExponent)
    {f : ℝ → ℝ} {M : NNReal} (hf : LipschitzWith M f) (hp : Function.Periodic f 1)
    (hint : Integrable (fun X : Configuration N => hessPairSum s.val (N : ℕ) f X.val)
      (gibbsMeasure P N)) :
    ∫ X : Configuration N, hessPairSum s.val (N : ℕ) f X.val ∂gibbsMeasure P N =
      (N : ℝ) ^ 2 * (∫ u in (0 : ℝ)..1, hessBackground s.val f u) +
        ∫ X : Configuration N, hessFluctExpansion s.val (N : ℕ) f X.val ∂gibbsMeasure P N := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  obtain ⟨B, hB0, hB⟩ := exists_hessBackground_le s hf hp
  -- The background, as a one-periodic function on the circle.
  have hGper : Function.Periodic (fun a => hessBackground s.val f a) 1 :=
    fun a => hessBackground_add_one s.val hp a
  have hGmeas : Measurable (fun a => hessBackground s.val f a) :=
    measurable_hessBackground s.val hf.continuous
  set Gc : UnitAddCircle → ℝ := hGper.lift with hGc
  have hGccoe : ∀ x : ℝ, Gc (x : UnitAddCircle) = hessBackground s.val f x :=
    fun x => hGper.lift_coe x
  have hGcmeas : Measurable Gc := measurable_periodic_circle_lift hGmeas hGper
  have hGcbd : ∀ t : UnitAddCircle, ‖Gc t‖ ≤ B := by
    intro t
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [show ((QuotientAddGroup.mk a : UnitAddCircle)) = (a : UnitAddCircle) from rfl, hGccoe,
      Real.norm_eq_abs]
    exact hB a
  have hGcmem : MemLp Gc 2 volume :=
    MemLp.of_bound hGcmeas.aestronglyMeasurable B (Filter.Eventually.of_forall hGcbd)
  -- Each particle has the uniform law, so the background sum has the period integral.
  have hcoord : ∀ i : Fin (N : ℕ), Integrable
      (fun X : Configuration N => Gc ((X.val i : ℝ) : UnitAddCircle)) (gibbsMeasure P N) :=
    fun i => (memLp_comp_coord P N i hGcmem).integrable one_le_two
  have hmarg : ∀ i : Fin (N : ℕ), ∫ X : Configuration N, Gc ((X.val i : ℝ) : UnitAddCircle)
      ∂gibbsMeasure P N = ∫ t : UnitAddCircle, Gc t :=
    fun i => integral_comp_coord P N i hGcmem
  have hcirc : ∫ t : UnitAddCircle, Gc t = ∫ u in (0 : ℝ)..1, hessBackground s.val f u := by
    rw [← UnitAddCircle.intervalIntegral_preimage 0 Gc]
    simp only [zero_add, hGccoe]
  have hsum : Integrable (fun X : Configuration N =>
      ∑ i : Fin (N : ℕ), Gc ((X.val i : ℝ) : UnitAddCircle)) (gibbsMeasure P N) :=
    integrable_finsetSum _ fun i _ => hcoord i
  -- Pointwise, the expansion is the pair sum minus the background sum plus a constant.
  have hexp : ∀ X : Configuration N, hessFluctExpansion s.val (N : ℕ) f X.val =
      hessPairSum s.val (N : ℕ) f X.val - 2 * (N : ℝ) *
        (∑ i : Fin (N : ℕ), Gc ((X.val i : ℝ) : UnitAddCircle)) +
        (N : ℝ) ^ 2 * ∫ u in (0 : ℝ)..1, hessBackground s.val f u := by
    intro X
    unfold hessFluctExpansion
    simp only [hGccoe]
  have hsumc : Integrable (fun X : Configuration N =>
      2 * (N : ℝ) * ∑ i : Fin (N : ℕ), Gc ((X.val i : ℝ) : UnitAddCircle)) (gibbsMeasure P N) :=
    hsum.const_mul _
  have hA : Integrable (fun X : Configuration N =>
      hessPairSum s.val (N : ℕ) f X.val -
        2 * (N : ℝ) * ∑ i : Fin (N : ℕ), Gc ((X.val i : ℝ) : UnitAddCircle)) (gibbsMeasure P N) :=
    hint.sub hsumc
  have e1 : ∫ X : Configuration N, (hessPairSum s.val (N : ℕ) f X.val -
        2 * (N : ℝ) * ∑ i : Fin (N : ℕ), Gc ((X.val i : ℝ) : UnitAddCircle)) ∂gibbsMeasure P N =
      ∫ X : Configuration N, hessPairSum s.val (N : ℕ) f X.val ∂gibbsMeasure P N -
        ∫ X : Configuration N, 2 * (N : ℝ) * ∑ i : Fin (N : ℕ), Gc ((X.val i : ℝ) : UnitAddCircle)
          ∂gibbsMeasure P N :=
    integral_sub hint hsumc
  have e2 : ∫ X : Configuration N, 2 * (N : ℝ) * ∑ i : Fin (N : ℕ), Gc ((X.val i : ℝ) : UnitAddCircle)
      ∂gibbsMeasure P N = 2 * (N : ℝ) * ∑ i : Fin (N : ℕ), ∫ t : UnitAddCircle, Gc t := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hcoord i]
    simp only [hmarg]
  have e3 : ∫ X : Configuration N, (hessPairSum s.val (N : ℕ) f X.val -
        2 * (N : ℝ) * ∑ i : Fin (N : ℕ), Gc ((X.val i : ℝ) : UnitAddCircle) +
        (N : ℝ) ^ 2 * ∫ u in (0 : ℝ)..1, hessBackground s.val f u) ∂gibbsMeasure P N =
      ∫ X : Configuration N, (hessPairSum s.val (N : ℕ) f X.val -
        2 * (N : ℝ) * ∑ i : Fin (N : ℕ), Gc ((X.val i : ℝ) : UnitAddCircle)) ∂gibbsMeasure P N +
        (N : ℝ) ^ 2 * ∫ u in (0 : ℝ)..1, hessBackground s.val f u := by
    rw [integral_add hA (integrable_const _), integral_const]
    simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), e3, e1, e2, hcirc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The Gibbs mean of the Hessian pair sum of a loop field: the integrability of the pair sum comes
from the moments of the Hessian quadratic term (`loop_moments`), since that term equals `β N^{-s}`
times the pair sum (`hessianQuadratic_eq_pairSum`). -/
theorem integral_hessPairSum (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val) :
    ∫ X : Configuration N, hessPairSum (parametersExponent P).val (N : ℕ)
        (loopScaleField ℓ.val ψ.val) X.val ∂gibbsMeasure P N =
      (N : ℝ) ^ 2 * (∫ u in (0 : ℝ)..1,
          hessBackground (parametersExponent P).val (loopScaleField ℓ.val ψ.val) u) +
        ∫ X : Configuration N, hessFluctExpansion (parametersExponent P).val (N : ℕ)
          (loopScaleField ℓ.val ψ.val) X.val ∂gibbsMeasure P N := by
  obtain ⟨M, hM⟩ := loopScaleField_lipschitz ψ
  have hp : Function.Periodic (loopScaleField ℓ.val ψ.val) 1 :=
    loopScaleField_periodic ψ.property.1
  have hQ : Integrable (fun X : Configuration N => hessianQuadratic P N ℓ ψ X)
      (gibbsMeasure P N) := by
    have h := (loop_moments P hPL N ℓ ψ).2 1 one_pos
    have h' : Integrable (fun X : Configuration N => ‖hessianQuadratic P N ℓ ψ X‖)
        (gibbsMeasure P N) := by
      simpa [Real.norm_eq_abs] using h
    exact (integrable_norm_iff
      (measurable_hessianQuadratic P N ℓ ψ).aestronglyMeasurable).mp h'
  have hcst : P.val.1 * (N : ℝ) ^ (-(parametersExponent P).val) ≠ 0 :=
    mul_ne_zero (ne_of_gt P.property.1)
      (Real.rpow_pos_of_pos (by exact_mod_cast N.pos) _).ne'
  have hint : Integrable (fun X : Configuration N => hessPairSum (parametersExponent P).val
      (N : ℕ) (loopScaleField ℓ.val ψ.val) X.val) (gibbsMeasure P N) := by
    have heq : (fun X : Configuration N => hessPairSum (parametersExponent P).val (N : ℕ)
        (loopScaleField ℓ.val ψ.val) X.val) =
        fun X : Configuration N => (P.val.1 * (N : ℝ) ^ (-(parametersExponent P).val))⁻¹ *
          hessianQuadratic P N ℓ ψ X := by
      funext X
      rw [hessianQuadratic_eq_pairSum, inv_mul_cancel_left₀ hcst]
      rfl
    rw [heq]
    exact hQ.const_mul _
  exact integral_hessPairSum_of_integrable P N (parametersExponent P) hM hp hint

end Riesz1

end

end
