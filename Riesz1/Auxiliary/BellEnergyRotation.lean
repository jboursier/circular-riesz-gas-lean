/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellEnergyIntegrability
public import Riesz1.Variance.MicroLocalIndependence

/-!
# Rotation averaging of a quadratic particle pair

The particle-particle conditioning step in Lemma B.1.
The common rotation is uniform and independent of each block length.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ContDiff

namespace Riesz1

/-- The pair kernel in common-rotation and microscopic-displacement coordinates. -/
def bellRotationKernel (s : ℝ) (N : ℕ+) (f : ℝ → ℝ) (hp : Function.Periodic f 1)
    (p : UnitAddCircle × ℝ) : ℝ :=
  (N : ℝ) ^ (-s) * iteratedDeriv 2 (hurwitzKernel s) (p.2 / N) *
    (hp.lift (p.1 + ((p.2 / N : ℝ) : UnitAddCircle)) - hp.lift p.1) ^ 2

lemma measurable_bellRotationKernel (s : ℝ) (N : ℕ+) {f : ℝ → ℝ}
    (hf : Continuous f) (hp : Function.Periodic f 1) :
    Measurable (bellRotationKernel s N f hp) := by
  have hfc := continuous_lift_periodic hf hp
  have harg : Continuous (fun p : UnitAddCircle × ℝ => p.1 + ((p.2 / N : ℝ) : UnitAddCircle)) := by
    fun_prop
  unfold bellRotationKernel
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (measurable_const.mul ((measurable_deriv (deriv (hurwitzKernel s))).comp
    (measurable_snd.div_const _))).mul
      (((hfc.comp harg).measurable.sub (hfc.measurable.comp measurable_fst)).pow_const 2)

/-- Averaging over the common rotation gives exactly the scalar kernel. -/
lemma integral_bellRotationKernel (s : ℝ) (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ)
    (hp : Function.Periodic ψ ℓ⁻¹) (y : ℝ) :
    (∫ x : UnitAddCircle, bellRotationKernel s N (loopScaleField ℓ ψ)
      (loopScaleField_periodic hp) (x, y)) = bellKernel s N ℓ ψ y := by
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
  simp only [zero_add]
  have he (x : ℝ) : bellRotationKernel s N (loopScaleField ℓ ψ)
      (loopScaleField_periodic hp) ((x : UnitAddCircle), y) =
      ((N : ℝ) ^ (-s) * ℓ ^ 2 * iteratedDeriv 2 (hurwitzKernel s) (y / N)) *
        (ψ ((x + y / N) / ℓ) - ψ (x / ℓ)) ^ 2 := by
    unfold bellRotationKernel
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe, Function.Periodic.lift_coe]
    unfold loopScaleField
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- Joint law of the rotation and a block, in the form used for conditioning. -/
lemma bell_joint_rotation_block (P : Parameters) (N : ℕ+) (i : ℤ) (k : ℕ) :
    (gibbsMeasure P N).map (fun X : Configuration N =>
      ((cyclicLift X i : UnitAddCircle), blockLength X i k)) =
        (volume : Measure UnitAddCircle).prod
          ((gibbsMeasure P N).map (fun X : Configuration N => blockLength X i k)) := by
  have := (modelWellDefined P N).2.2
  have hr : AEMeasurable (fun X : Configuration N => (cyclicLift X i : UnitAddCircle))
      (gibbsMeasure P N) := by
    simpa only [Function.comp_def] using
      (measurable_coe_circle.comp (measurable_cyclicLift i)).aemeasurable (μ := gibbsMeasure P N)
  have hb := (measurable_blockLength i k).aemeasurable (μ := gibbsMeasure P N)
  rw [(indepFun_iff_map_prod_eq_prod_map_map hr hb).mp
    (indepFun_cyclicLift_blockLength P N i i k), map_cyclicLift_gibbsMeasure]

/-- The formula in rotation coordinates agrees with the original pair kernel. -/
lemma bellRotationKernel_coe (s : ℝ) (N : ℕ+) (f : ℝ → ℝ) (hp : Function.Periodic f 1)
    (a b : ℝ) :
    bellRotationKernel s N f hp ((a : UnitAddCircle), (N : ℝ) * (b - a)) =
      (N : ℝ) ^ (-s) * bellPairKernel s f a b := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have he : (N : ℝ) * (b - a) / N = b - a := by field_simp
  unfold bellRotationKernel
  rw [he, ← AddCircle.coe_add, Function.Periodic.lift_coe, Function.Periodic.lift_coe,
    show a + (b - a) = b by ring, show b - a = -(a - b) by ring, iteratedDeriv_two_neg]
  unfold bellPairKernel
  ring

lemma measurable_bellKernel {s : ℝ} {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : Measurable (bellKernel s N ℓ ψ) := by
  unfold bellKernel
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (measurable_const.mul ((measurable_deriv (deriv (hurwitzKernel s))).comp
    (measurable_id.div_const _))).mul
      ((continuous_bellIncrement hℓ hψ).measurable.comp (measurable_id.div_const _))

/-- The expectation of an off-diagonal particle pair, after averaging the common rotation. -/
theorem integral_bellPair_eq_integral_bellKernel (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (i j : Fin (N : ℕ)) (hij : i < j) :
    (∫ X : Configuration N, (N : ℝ) ^ (-P.1.2) *
      bellPairKernel P.1.2 (loopScaleField ℓ.val ψ.val) (X.val i) (X.val j) ∂gibbsMeasure P N) =
      ∫ X : Configuration N, bellKernel P.1.2 N ℓ.val ψ.val
        (blockLength X (i : ℕ) ((j : ℕ) - (i : ℕ))) ∂gibbsMeasure P N := by
  have := (modelWellDefined P N).2.2
  let f := loopScaleField ℓ.val ψ.val
  have hp : Function.Periodic f 1 := loopScaleField_periodic ψ.2.1
  let k := (j : ℕ) - (i : ℕ)
  let F := bellRotationKernel P.1.2 N f hp
  let J := fun X : Configuration N => ((cyclicLift X (i : ℕ) : UnitAddCircle), blockLength X (i : ℕ) k)
  have hJ : Measurable J := by
    simpa only [Function.comp_def] using
      (measurable_coe_circle.comp (measurable_cyclicLift (i : ℕ))).prodMk
        (measurable_blockLength (i : ℕ) k)
  have hF : Measurable F := measurable_bellRotationKernel _ _
    (loopScaleField_contDiff hψ).continuous hp
  have hpoint (X : Configuration N) : F (J X) =
      (N : ℝ) ^ (-P.1.2) * bellPairKernel P.1.2 f (X.val i) (X.val j) := by
    have hidx : (i : ℤ) + k = (j : ℤ) := by dsimp [k]; omega
    dsimp [F, J]
    unfold blockLength
    rw [hidx, cyclicLift_natCast X i, cyclicLift_natCast X j]
    exact bellRotationKernel_coe _ _ _ _ _ _
  obtain ⟨M, hf⟩ := loopScaleField_lipschitz ψ
  have hi : Integrable (fun X : Configuration N => F (J X)) (gibbsMeasure P N) := by
    have hh := (bellPair_particle_integrable P hPL N hf hp i j (ne_of_lt hij)).const_mul
      ((N : ℝ) ^ (-P.1.2))
    exact hh.congr (ae_of_all _ fun X => (hpoint X).symm)
  have hiMap : Integrable F ((gibbsMeasure P N).map J) :=
    (integrable_map_measure hF.aestronglyMeasurable hJ.aemeasurable).mpr
      (by simpa only [Function.comp_def] using hi)
  have hLaw : (gibbsMeasure P N).map J = (volume : Measure UnitAddCircle).prod
      ((gibbsMeasure P N).map (fun X : Configuration N => blockLength X (i : ℕ) k)) :=
    bell_joint_rotation_block P N (i : ℕ) k
  rw [hLaw] at hiMap
  calc
    _ = (∫ X : Configuration N, F (J X) ∂gibbsMeasure P N) := by
      apply integral_congr_ae
      exact ae_of_all _ fun X => (hpoint X).symm
    _ = (∫ p, F p ∂(gibbsMeasure P N).map J) :=
      (integral_map hJ.aemeasurable hF.aestronglyMeasurable).symm
    _ = (∫ p, F p ∂(volume : Measure UnitAddCircle).prod
        ((gibbsMeasure P N).map (fun X : Configuration N => blockLength X (i : ℕ) k))) := by rw [hLaw]
    _ = (∫ y, (∫ x : UnitAddCircle, F (x, y))
        ∂(gibbsMeasure P N).map (fun X : Configuration N => blockLength X (i : ℕ) k)) :=
          integral_prod_symm F hiMap
    _ = (∫ y, bellKernel P.1.2 N ℓ.val ψ.val y
        ∂(gibbsMeasure P N).map (fun X : Configuration N => blockLength X (i : ℕ) k)) := by
          apply integral_congr_ae
          exact ae_of_all _ fun y => integral_bellRotationKernel _ _ _ _ ψ.2.1 y
    _ = _ := integral_map (measurable_blockLength _ _).aemeasurable
      (measurable_bellKernel ℓ.2.1 hψ).aestronglyMeasurable


end Riesz1

end
