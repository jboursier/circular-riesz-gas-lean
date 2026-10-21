/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellEnergyRotation
public import Riesz1.ToMathlib.PeriodicCircleLift

/-!
# Background terms in the quadratic energy

Uniform particle marginals identify the mean particle-background term with the
background-background term. Absolute integrability justifies displacement Fubini.
Rescaling that displacement identifies the scalar kernel in Lemma B.1.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

lemma bellPairKernel_periodic_left (s : ℝ) {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (y : ℝ) : Function.Periodic (fun x => bellPairKernel s f x y) 1 := by
  intro x
  dsimp only [bellPairKernel]
  rw [show x + 1 - y = (x - y) + 1 by ring, iteratedDeriv_two_periodic, hp]

/-- Integration of any measurable periodic observable against a one-particle marginal. -/
lemma bell_integral_periodic_particle (P : Parameters) (N : ℕ+) {f : ℝ → ℝ}
    (hf : Measurable f) (hp : Function.Periodic f 1) (i : Fin (N : ℕ)) :
    (∫ X : Configuration N, f (X.val i) ∂gibbsMeasure P N) = ∫ x in (0 : ℝ)..1, f x := by
  have hm := measurable_periodic_circle_lift hf hp
  have hx := measurable_coe_circle.comp (measurable_cyclicLift (N := N) (i : ℕ))
  calc
    _ = ∫ X : Configuration N, hp.lift (cyclicLift X (i : ℕ) : UnitAddCircle)
        ∂gibbsMeasure P N := by
      apply integral_congr_ae
      exact ae_of_all _ fun X => by
        dsimp only
        rw [hp.lift_coe, cyclicLift_natCast]
    _ = ∫ x : UnitAddCircle, hp.lift x
        ∂(gibbsMeasure P N).map (fun X : Configuration N => (cyclicLift X (i : ℕ) : UnitAddCircle)) :=
      (integral_map hx.aemeasurable hm.aestronglyMeasurable).symm
    _ = ∫ x : UnitAddCircle, hp.lift x := by rw [map_cyclicLift_gibbsMeasure]
    _ = _ := by
      rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
      simp only [zero_add, hp.lift_coe]

/-- A particle-background term has the same mean as the double background. -/
theorem integral_bell_particle_background (P : Parameters) (N : ℕ+)
    {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) (i : Fin (N : ℕ)) :
    (∫ X : Configuration N, (∫ y in (0 : ℝ)..1, bellPairKernel P.1.2 f (X.val i) y)
      ∂gibbsMeasure P N) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, bellPairKernel P.1.2 f x y := by
  apply bell_integral_periodic_particle P N (measurable_bellPair_background _ hf) _ i
  intro x
  apply intervalIntegral.integral_congr
  intro y _
  exact bellPairKernel_periodic_left _ hp y x

/-- Absolute integrability on the background rotation-displacement product. -/
lemma bellPair_displacement_product_integrable (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    Integrable (fun p : ℝ × ℝ => bellPairIntegrand s.val f p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨K, _, _, hb⟩ := bellPair_majorant s hf hp
  have hmaj := ((integrableOn_rpow_majorant s.2.2).const_mul K).comp_snd
    (volume.restrict (Ioo (0 : ℝ) 1))
  have hm : Measurable (fun p : ℝ × ℝ => bellPairIntegrand s.val f p.1 p.2) := by
    have he : (fun p : ℝ × ℝ => bellPairIntegrand s.val f p.1 p.2) =
        (fun p : ℝ × ℝ => bellPairKernel s.val f p.1 p.2) ∘
          (fun p : ℝ × ℝ => (p.1, p.1 - p.2)) := by
      funext p
      dsimp [bellPairIntegrand, bellPairKernel]
      rw [sub_sub_cancel]
      ring
    rw [he]
    exact (measurable_bellPairKernel _ hf.continuous).comp
      (measurable_fst.prodMk (measurable_fst.sub measurable_snd))
  apply hmaj.mono' hm.aestronglyMeasurable
  have hmem : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)), p.2 ∈ Ioo (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioo)).mpr
    exact ae_of_all _ fun _ => ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with p hp'
  simpa only [Real.norm_eq_abs] using hb p.1 p.2 hp'.1 hp'.2

/-- The double background is the integral of `q` in microscopic units, divided by `N`. -/
theorem bell_background_eq_integral_kernel (s : RieszExponent) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val) :
    (N : ℝ) ^ (-s.val) *
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        bellPairKernel s.val (loopScaleField ℓ.val ψ.val) x y) =
      (N : ℝ)⁻¹ * ∫ y in (0 : ℝ)..(N : ℝ), bellKernel s.val N ℓ.val ψ.val y := by
  let f := loopScaleField ℓ.val ψ.val
  have hp : Function.Periodic f 1 := loopScaleField_periodic ψ.2.1
  obtain ⟨M, hf⟩ := loopScaleField_lipschitz ψ
  have hswap : (∫ x in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, bellPairIntegrand s.val f x u) =
      ∫ u in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, bellPairIntegrand s.val f x u := by
    simp_rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    exact integral_integral_swap (bellPair_displacement_product_integrable s hf hp)
  have hinner (u : ℝ) : (N : ℝ) ^ (-s.val) *
      (∫ x in (0 : ℝ)..1, bellPairIntegrand s.val f x u) =
      bellKernel s.val N ℓ.val ψ.val ((N : ℝ) * u) := by
    have he (x : ℝ) : bellPairIntegrand s.val f x u =
        (ℓ.val ^ 2 * iteratedDeriv 2 (hurwitzKernel s.val) u) *
          (ψ.val ((x + -u) / ℓ.val) - ψ.val (x / ℓ.val)) ^ 2 := by
      dsimp [bellPairIntegrand, f, loopScaleField]
      rw [sub_eq_add_neg x u]
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul]
    change (N : ℝ) ^ (-s.val) *
      (ℓ.val ^ 2 * iteratedDeriv 2 (hurwitzKernel s.val) u * bellIncrement ℓ.val ψ.val (-u)) = _
    rw [bellIncrement_neg ψ.2.1]
    unfold bellKernel
    rw [mul_div_cancel_left₀ u (show (N : ℝ) ≠ 0 by exact_mod_cast N.ne_zero)]
    ring
  calc
    _ = (N : ℝ) ^ (-s.val) *
        (∫ x in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, bellPairIntegrand s.val f x u) := by
      congr 1
      exact intervalIntegral.integral_congr fun x _ => bellPair_integral_displacement _ hp x
    _ = (N : ℝ) ^ (-s.val) *
        (∫ u in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, bellPairIntegrand s.val f x u) := by rw [hswap]
    _ = ∫ u in (0 : ℝ)..1, bellKernel s.val N ℓ.val ψ.val ((N : ℝ) * u) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun u _ => hinner u
    _ = _ := by
      rw [intervalIntegral.integral_comp_mul_left _ (show (N : ℝ) ≠ 0 by exact_mod_cast N.ne_zero)]
      simp only [mul_zero, mul_one, smul_eq_mul]

end Riesz1

end
