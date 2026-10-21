/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryMixedHessian
public import Riesz1.Variance.LoopScaleIntegrability
public import Riesz1.Kernel.MeanFieldEnergyKernel
public import Riesz1.ToMathlib.CircleFourierDerivativeShift

/-!
# The Hessian pair kernel and its particle-background integral

This is part of Proposition 5.6. For a one-periodic Lipschitz field `f`, the
Hessian pair kernel is `K_f(a, b) = g_s''(a - b) (f a - f b)²`, and the Hessian quadratic term is
`β N^{-s}` times its sum over ordered pairs of distinct particles (`hessianQuadratic_eq_pairSum`).
This file records the kernel, its background integral `G_f(a) = ∫₀¹ K_f(a, y) dy`, and the
estimates that make these integrals meaningful: a pointwise bound by a power of the circle
distance, a bound on `G_f` uniform in `a`, and measurability.

The main results are `Riesz1.exists_hessKernel_le`, `Riesz1.exists_hessBackground_le` and
`Riesz1.measurable_hessBackground`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology UnitAddCircle
open scoped ContDiff

namespace Riesz1

/-- The Hessian pair kernel `K_f(a, b) = g_s''(a - b) (f a - f b)²`. -/
noncomputable def hessKernel (s : ℝ) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (deriv (hurwitzKernel s)) (a - b) * (f a - f b) ^ 2

/-- The particle-background integral `G_f(a) = ∫₀¹ K_f(a, y) dy` of the Hessian pair kernel. -/
noncomputable def hessBackground (s : ℝ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, hessKernel s f a y

/-- The second derivative of the kernel is one-periodic. -/
private lemma deriv_deriv_hurwitzKernel_periodic (s : ℝ) :
    Function.Periodic (deriv (deriv (hurwitzKernel s))) 1 :=
  CircleFourier.periodic_deriv (CircleFourier.periodic_deriv fun x => hurwitzKernel_add_one s x)

/-- The Hessian pair kernel is one-periodic in its first argument when `f` is one-periodic. -/
lemma hessKernel_add_one_left (s : ℝ) {f : ℝ → ℝ} (hp : Function.Periodic f 1) (a b : ℝ) :
    hessKernel s f (a + 1) b = hessKernel s f a b := by
  unfold hessKernel
  rw [hp a, show a + 1 - b = (a - b) + 1 by ring,
    deriv_deriv_hurwitzKernel_periodic s (a - b)]

/-- The Hessian pair kernel is one-periodic in its second argument when `f` is one-periodic. -/
lemma hessKernel_add_one_right (s : ℝ) {f : ℝ → ℝ} (hp : Function.Periodic f 1) (a b : ℝ) :
    hessKernel s f a (b + 1) = hessKernel s f a b := by
  unfold hessKernel
  rw [hp b, show a - (b + 1) = (a - b) + (-1) by ring]
  have h := deriv_deriv_hurwitzKernel_periodic s ((a - b) + (-1))
  rw [show (a - b) + (-1) + 1 = a - b by ring] at h
  rw [h]

/-- The Hessian pair kernel is bounded by a constant multiple of a power of the circle distance of
`a - b` to zero, with the constant depending only on `s` and on the Lipschitz constant of `f`. -/
lemma exists_hessKernel_le (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, ((a - b : ℝ) : UnitAddCircle) ≠ 0 →
      |hessKernel s.val f a b| ≤ K * dist ((a - b : ℝ) : UnitAddCircle) 0 ^ (-s.val) := by
  obtain ⟨C, hC, hgb⟩ := deriv_deriv_hurwitzKernel_bound s.val s.property.1 s.property.2
  refine ⟨C * (M : ℝ) ^ 2, mul_nonneg hC.le (sq_nonneg _), fun a b hab => ?_⟩
  set d := dist ((a - b : ℝ) : UnitAddCircle) 0 with hd
  have hdpos : 0 < d := dist_pos.mpr hab
  have hψ : |f a - f b| ≤ (M : ℝ) * d := by
    have h := loopScale_lipschitz_increment hf hp b (a - b)
    rwa [show b + (a - b) = a by ring] at h
  have hk : |deriv (deriv (hurwitzKernel s.val)) (a - b)| ≤ C * d ^ (-s.val - 2) :=
    hgb (a - b) hab
  have he : d ^ (-s.val - 2) * d ^ 2 = d ^ (-s.val) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hdpos]
    congr 1
    push_cast
    ring
  unfold hessKernel
  rw [abs_mul, abs_of_nonneg (sq_nonneg (f a - f b))]
  have h2 : (f a - f b) ^ 2 ≤ ((M : ℝ) * d) ^ 2 :=
    sq_le_sq' (abs_le.mp hψ).1 (abs_le.mp hψ).2
  calc |deriv (deriv (hurwitzKernel s.val)) (a - b)| * (f a - f b) ^ 2
      ≤ (C * d ^ (-s.val - 2)) * ((M : ℝ) * d) ^ 2 :=
        mul_le_mul hk h2 (sq_nonneg _) (mul_nonneg hC.le (Real.rpow_nonneg hdpos.le _))
    _ = (C * (M : ℝ) ^ 2) * d ^ (-s.val) := by rw [← he]; ring

/-- The circle distance power `dist(z, ℤ)^{-s}` is one-periodic. -/
lemma periodic_dist_rpow (s : ℝ) :
    Function.Periodic (fun z : ℝ => dist (z : UnitAddCircle) 0 ^ (-s)) 1 := by
  intro z
  simp only
  rw [AddCircle.coe_add_period]

/-- The circle distance power is measurable. -/
lemma measurable_dist_rpow (s : ℝ) :
    Measurable (fun z : ℝ => dist (z : UnitAddCircle) 0 ^ (-s)) :=
  ((continuous_quotient_mk'.dist continuous_const).measurable).pow_const _

/-- The integral of the circle distance power over one period does not depend on the shift. -/
lemma integral_dist_rpow_shift (s a : ℝ) :
    ∫ y in (0 : ℝ)..1, dist ((a - y : ℝ) : UnitAddCircle) 0 ^ (-s) =
      ∫ z in (0 : ℝ)..1, dist (z : UnitAddCircle) 0 ^ (-s) := by
  have hp := periodic_dist_rpow s
  have h1 : ∫ y in (0 : ℝ)..1, dist ((a - y : ℝ) : UnitAddCircle) 0 ^ (-s) =
      ∫ x in (a - 1)..(a - 0), dist (x : UnitAddCircle) 0 ^ (-s) :=
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => dist (x : UnitAddCircle) 0 ^ (-s)) a
  have e : a - 0 = (a - 1) + 1 := by ring
  rw [h1, e, hp.intervalIntegral_add_eq (a - 1) 0, zero_add]

/-- The circle distance power is interval integrable over one period. -/
lemma intervalIntegrable_dist_rpow {s : ℝ} (hs1 : s < 1) :
    IntervalIntegrable (fun z : ℝ => dist (z : UnitAddCircle) 0 ^ (-s)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine Integrable.mono' (integrableOn_rpow_majorant hs1)
    (measurable_dist_rpow s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)]
  exact dist_rpow_le_majorant (s := s) hz.1 hz.2

/-- The Hessian pair kernel is jointly measurable for a continuous field. -/
lemma measurable_hessKernel_pair (s : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun p : ℝ × ℝ => hessKernel s f p.1 p.2) := by
  unfold hessKernel
  refine Measurable.mul ?_ ?_
  · exact (measurable_deriv (deriv (hurwitzKernel s))).comp (measurable_fst.sub measurable_snd)
  · exact (((hf.measurable.comp measurable_fst).sub (hf.measurable.comp measurable_snd))).pow_const 2

/-- The particle-background integral is measurable in the particle position. -/
lemma measurable_hessBackground (s : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun a : ℝ => hessBackground s f a) := by
  simp_rw [hessBackground, intervalIntegral.integral_of_le zero_le_one]
  exact (((measurable_hessKernel_pair s hf).stronglyMeasurable).integral_prod_right').measurable

/-- The particle-background integral is one-periodic in the particle position. -/
lemma hessBackground_add_one {f : ℝ → ℝ} (s : ℝ) (hp : Function.Periodic f 1) (a : ℝ) :
    hessBackground s f (a + 1) = hessBackground s f a := by
  unfold hessBackground
  simp_rw [hessKernel_add_one_left s hp]

/-- The particle-background integral is bounded uniformly in the particle position. -/
lemma exists_hessBackground_le (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ, |hessBackground s.val f a| ≤ B := by
  obtain ⟨K, hK0, hK⟩ := exists_hessKernel_le s hf hp
  refine ⟨K * ∫ z in (0 : ℝ)..1, dist (z : UnitAddCircle) 0 ^ (-s.val),
    mul_nonneg hK0 (intervalIntegral.integral_nonneg zero_le_one
      fun z _ => Real.rpow_nonneg dist_nonneg _), fun a => ?_⟩
  -- The set where `a - y` is a lattice point is countable, hence null.
  have hcount : Set.Countable {y : ℝ | ((a - y : ℝ) : UnitAddCircle) = 0} := by
    refine (Set.countable_range fun k : ℤ => a - (k : ℝ)).mono ?_
    intro y hy
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hy
    exact ⟨n, by simp only [zsmul_eq_mul, mul_one] at hn; linarith⟩
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), ((a - y : ℝ) : UnitAddCircle) ≠ 0 := by
    exact ae_iff.mpr (by simp only [ne_eq, not_not]; exact hcount.measure_zero volume)
  have hbound : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Ioc (0 : ℝ) 1 →
      ‖hessKernel s.val f a y‖ ≤ K * dist ((a - y : ℝ) : UnitAddCircle) 0 ^ (-s.val) := by
    filter_upwards [hae] with y hy _
    rw [Real.norm_eq_abs]
    exact hK a y hy
  have hint : IntervalIntegrable
      (fun y : ℝ => K * dist ((a - y : ℝ) : UnitAddCircle) 0 ^ (-s.val)) volume 0 1 := by
    refine IntervalIntegrable.const_mul ?_ K
    have h0 : IntervalIntegrable (fun z : ℝ => dist (z : UnitAddCircle) 0 ^ (-s.val)) volume
        0 (0 + 1) := by
      simpa using intervalIntegrable_dist_rpow s.property.2
    have hφ := (periodic_dist_rpow s.val).intervalIntegrable (t := 0) one_ne_zero h0 (a - 1) a
    have h := hφ.comp_sub_left a
    rw [sub_self, sub_sub_cancel] at h
    exact h.symm
  calc |hessBackground s.val f a|
      = ‖∫ y in (0 : ℝ)..1, hessKernel s.val f a y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y in (0 : ℝ)..1, K * dist ((a - y : ℝ) : UnitAddCircle) 0 ^ (-s.val) :=
        intervalIntegral.norm_integral_le_of_norm_le zero_le_one hbound hint
    _ = K * ∫ z in (0 : ℝ)..1, dist (z : UnitAddCircle) 0 ^ (-s.val) := by
        rw [intervalIntegral.integral_const_mul, integral_dist_rpow_shift]

end Riesz1

end

end
