/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellEnergyDefs
public import Riesz1.Variance.LoopIBPPairs

/-!
# Absolute integrability of the quadratic loop

The integrability clause of Lemma B.1.
Background integrals are dominated by the integrable power `|u|^(-s)`.
Particle terms are dominated by the inverse-gap power sum.
No rigidity hypothesis is needed for any result in this file.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

lemma bellPairIntegrand_periodic (s : ℝ) {f : ℝ → ℝ} (hp : Function.Periodic f 1) (x : ℝ) :
    Function.Periodic (bellPairIntegrand s f x) 1 := by
  intro u
  unfold bellPairIntegrand
  rw [iteratedDeriv_two_periodic, show x - (u + 1) = (x - u) - 1 by ring, hp.sub_eq]

lemma bellPair_integral_displacement (s : ℝ) {f : ℝ → ℝ}
    (hp : Function.Periodic f 1) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, bellPairKernel s f x y) =
      ∫ u in (0 : ℝ)..1, bellPairIntegrand s f x u := by
  have he (y : ℝ) : bellPairKernel s f x y = bellPairIntegrand s f x (x - y) := by
    unfold bellPairKernel bellPairIntegrand
    rw [sub_sub_cancel]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_comp_sub_left, sub_zero]
  have ht := (bellPairIntegrand_periodic s hp x).intervalIntegral_add_eq (x - 1) 0
  simpa only [sub_add_cancel, zero_add] using ht

/-- Absolute convergence and a bound for all background terms, uniformly in the anchor. -/
theorem bellPair_background_integrals (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    (∀ x : ℝ, IntervalIntegrable (fun y => bellPairKernel s.val f x y) volume 0 1) ∧
    (∀ y : ℝ, IntervalIntegrable (fun x => bellPairKernel s.val f x y) volume 0 1) ∧
    IntervalIntegrable (fun x => ∫ y in (0 : ℝ)..1, bellPairKernel s.val f x y) volume 0 1 ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
      |∫ y in (0 : ℝ)..1, bellPairKernel s.val f x y| ≤ B := by
  obtain ⟨K, hK, _, hb⟩ := bellPair_majorant s hf hp
  have hmaj : IntervalIntegrable
      (fun u : ℝ => K * (u ^ (-s.val) + (1 - u) ^ (-s.val))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact (integrableOn_rpow_majorant s.2.2).const_mul K
  have hmeas : Measurable (fun p : ℝ × ℝ => bellPairIntegrand s.val f p.1 p.2) := by
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
  have hint (x : ℝ) : IntervalIntegrable (bellPairIntegrand s.val f x) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hmaj ⊢
    apply hmaj.mono' (hmeas.comp measurable_prodMk_left).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simpa only [Real.norm_eq_abs, Function.comp_apply] using hb x u hu.1 hu.2
  have hintK (x : ℝ) : IntervalIntegrable (fun y => bellPairKernel s.val f x y) volume 0 1 := by
    have hi := (bellPairIntegrand_periodic s.val hp x).intervalIntegrable (t := 0)
      one_ne_zero (by simpa only [zero_add] using hint x) (x - 1) x
    have hc := hi.comp_sub_left x
    rw [show x - (x - 1) = 1 by ring, sub_self] at hc
    apply hc.symm.congr
    intro y hy
    change bellPairIntegrand s.val f x (x - y) = bellPairKernel s.val f x y
    unfold bellPairIntegrand bellPairKernel
    rw [sub_sub_cancel]
    ring
  let B := ∫ u in (0 : ℝ)..1, K * (u ^ (-s.val) + (1 - u) ^ (-s.val))
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg zero_le_one
    (fun u hu => mul_nonneg hK (add_nonneg (Real.rpow_nonneg hu.1 _)
      (Real.rpow_nonneg (by linarith [hu.2]) _)))
  have hbound (x : ℝ) : |∫ y in (0 : ℝ)..1, bellPairKernel s.val f x y| ≤ B := by
    rw [bellPair_integral_displacement s.val hp x]
    have hh := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (f := bellPairIntegrand s.val f x) (g := fun u => K * (u ^ (-s.val) + (1 - u) ^ (-s.val)))
      (by
        filter_upwards [ae_ne_const (1 : ℝ)] with u hu1 hu
        rw [Real.norm_eq_abs]
        exact hb x u hu.1 (lt_of_le_of_ne hu.2 hu1)) hmaj
    simpa only [Real.norm_eq_abs] using hh
  refine ⟨hintK, ?_, ?_, B, hB, hbound⟩
  · intro y
    exact (hintK y).congr (fun x _ => bellPairKernel_symm s.val f y x)
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    apply (integrable_const B).mono' (measurable_bellPair_background _ hf.continuous).aestronglyMeasurable
    exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x

/-- Integrability of a background term after any measurable choice of its anchor. -/
theorem bellPair_background_comp_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) {x : Ω → ℝ} (hx : Measurable x) :
    Integrable (fun X => ∫ y in (0 : ℝ)..1, bellPairKernel s.val f (x X) y) μ := by
  obtain ⟨_, _, _, B, _, hbound⟩ := bellPair_background_integrals s hf hp
  have hmeas : Measurable (fun X => ∫ y in (0 : ℝ)..1, bellPairKernel s.val f (x X) y) := by
    simpa only [Function.comp_def] using
      (measurable_bellPair_background s.val hf.continuous).comp hx
  apply (integrable_const B).mono' hmeas.aestronglyMeasurable
  exact ae_of_all _ fun X => by simpa only [Real.norm_eq_abs] using hbound (x X)

/-- Absolute integrability of an off-diagonal particle pair. -/
theorem bellPair_particle_integrable (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) {f : ℝ → ℝ} {M : NNReal} (hf : LipschitzWith M f)
    (hp : Function.Periodic f 1) (i j : Fin (N : ℕ)) (hne : i ≠ j) :
    Integrable (fun X : Configuration N =>
      bellPairKernel (parametersExponent P).val f (X.val i) (X.val j)) (gibbsMeasure P N) := by
  let s := parametersExponent P
  obtain ⟨K, hK, hpoint, _⟩ := bellPair_majorant s hf hp
  have hG := integrable_gapPowerSum P hPL s.2.1 N
  have hcoord (i : Fin (N : ℕ)) : Measurable (fun X : Configuration N => X.val i) :=
    (measurable_pi_apply i).comp measurable_subtype_coe
  have hmeas : Measurable (fun X : Configuration N => bellPairKernel s.val f (X.val i) (X.val j)) := by
    simpa only [Function.comp_def] using (measurable_bellPairKernel s.val hf.continuous).comp
      ((hcoord i).prodMk (hcoord j))
  apply (hG.const_mul (K * (N : ℝ) ^ s.val)).mono' hmeas.aestronglyMeasurable
  exact ae_of_all _ fun X => by
    rw [Real.norm_eq_abs]
    calc _ ≤ K * dist ((X.val i - X.val j : ℝ) : UnitAddCircle) 0 ^ (-s.val) :=
        hpoint _ _ (coe_sub_ne_zero X hne)
      _ ≤ K * ((N : ℝ) ^ s.val * gapPowerSum s.val X) :=
        mul_le_mul_of_nonneg_left (dist_rpow_le_gapPowerSum X hne s.2.1.le) hK
      _ = _ := by ring

/-- Every quadratic loop is absolutely integrable, for every periodic Lipschitz
profile. This includes the integrability assertion of Lemma B.1. -/
theorem bell_quadratic_loop_integrable (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val) :
    Integrable (bellQuadraticLoop (parametersExponent P) N ℓ ψ) (gibbsMeasure P N) := by
  have := (modelWellDefined P N).2.2
  let s := parametersExponent P
  let f := loopScaleField ℓ.val ψ.val
  obtain ⟨M, hf⟩ := loopScaleField_lipschitz ψ
  have hp : Function.Periodic f 1 := loopScaleField_periodic ψ.2.1
  have hbg (i : Fin (N : ℕ)) : Integrable (fun X : Configuration N =>
      ∫ y in (0 : ℝ)..1, bellPairKernel s.val f (X.val i) y) (gibbsMeasure P N) :=
    bellPair_background_comp_integrable (gibbsMeasure P N) s hf hp
      ((measurable_pi_apply i).comp measurable_subtype_coe)
  have hbg' (i : Fin (N : ℕ)) : Integrable (fun X : Configuration N =>
      ∫ x in (0 : ℝ)..1, bellPairKernel s.val f x (X.val i)) (gibbsMeasure P N) := by
    have he : (fun X : Configuration N =>
        ∫ x in (0 : ℝ)..1, bellPairKernel s.val f x (X.val i)) =
        (fun X : Configuration N => ∫ y in (0 : ℝ)..1, bellPairKernel s.val f (X.val i) y) := by
      funext X
      apply intervalIntegral.integral_congr
      intro x hx
      exact bellPairKernel_symm s.val f x (X.val i)
    rw [he]
    exact hbg i
  have hpair (p : Fin (N : ℕ) × Fin (N : ℕ))
      (hp' : p ∈ (Finset.univ : Finset (Fin (N : ℕ))).offDiag) :
      Integrable (fun X : Configuration N => bellPairKernel s.val f (X.val p.1) (X.val p.2))
        (gibbsMeasure P N) :=
    bellPair_particle_integrable P hPL N hf hp p.1 p.2 (Finset.mem_offDiag.mp hp').2.2
  unfold bellQuadraticLoop
  change Integrable (fun X : Configuration N => (N : ℝ) ^ (-s.val) *
    ((∑ p ∈ (Finset.univ : Finset (Fin (N : ℕ))).offDiag,
      bellPairKernel s.val f (X.val p.1) (X.val p.2)) -
      (N : ℝ) * (∑ i : Fin (N : ℕ), ∫ y in (0 : ℝ)..1, bellPairKernel s.val f (X.val i) y) -
      (N : ℝ) * (∑ j : Fin (N : ℕ), ∫ x in (0 : ℝ)..1, bellPairKernel s.val f x (X.val j)) +
      (N : ℝ) ^ 2 * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, bellPairKernel s.val f x y)))
      (gibbsMeasure P N)
  have hpp := integrable_finsetSum _ hpair
  have hpb := (integrable_finsetSum Finset.univ (fun i _ => hbg i)).const_mul (N : ℝ)
  have hbp := (integrable_finsetSum Finset.univ (fun i _ => hbg' i)).const_mul (N : ℝ)
  have hc : Integrable (fun _X : Configuration N => (N : ℝ) ^ 2 *
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, bellPairKernel s.val f x y)
      (gibbsMeasure P N) := integrable_const _
  have hresult := (((hpp.sub hpb).sub hbp).add hc).const_mul ((N : ℝ) ^ (-s.val))
  exact hresult


end Riesz1

end
