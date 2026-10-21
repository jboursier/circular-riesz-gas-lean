/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Variational.MeanZeroPoisson
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Centering and the Poisson equation on a probability space

The mean and centered right-hand side live in scalar `L²`. The internal
existence criterion uses only the Sobolev norm identity, a unit with zero
gradient, and a Poincaré inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The continuous expectation functional on scalar `L²`. -/
def poissonMean : Lp ℝ 2 μ →L[ℝ] ℝ := innerSL ℝ (Lp.const 2 μ (1 : ℝ))

/-- The centered `L²` right-hand side of the scalar Poisson equation. -/
def poissonCenter (F : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  F - poissonMean μ F • Lp.const 2 μ (1 : ℝ)

theorem poissonMean_eq_integral (F : Lp ℝ 2 μ) :
    poissonMean μ F = ∫ x, F x ∂μ := by
  rw [poissonMean, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with x hx
  simp

theorem poissonMean_one : poissonMean μ (Lp.const 2 μ (1 : ℝ)) = 1 := by
  rw [poissonMean_eq_integral]
  exact (integral_congr_ae (Lp.coeFn_const 2 μ (1 : ℝ))).trans (by simp)

theorem poissonMean_center (F : Lp ℝ 2 μ) : poissonMean μ (poissonCenter μ F) = 0 := by
  simp [poissonCenter, poissonMean_one]

theorem poissonCenter_ae (F : Lp ℝ 2 μ) :
    poissonCenter μ F =ᵐ[μ] fun x => F x - ∫ y, F y ∂μ := by
  filter_upwards [Lp.coeFn_sub F (poissonMean μ F • Lp.const 2 μ (1 : ℝ)),
    Lp.coeFn_smul (poissonMean μ F) (Lp.const 2 μ (1 : ℝ)),
    Lp.coeFn_const 2 μ (1 : ℝ)] with x hsub hsmul hone
  dsimp only [poissonCenter]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hone]
  simp [poissonMean_eq_integral]

omit [IsProbabilityMeasure μ] in
theorem poisson_norm_sq (F : Lp ℝ 2 μ) : ‖F‖ ^ 2 = ∫ x, F x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [pow_two]

/-- The centered second moment in Hilbert coordinates. -/
theorem poisson_variance_eq (F : Lp ℝ 2 μ) :
    (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) =
      ‖F‖ ^ 2 - (poissonMean μ F) ^ 2 := by
  rw [WeightedSobolev.integral_sub_mean_sq (Lp.memLp F),
    ← poisson_norm_sq, poissonMean_eq_integral]

omit [IsProbabilityMeasure μ] in
/-- Scalar `L²` inner products are the integrals of products. -/
theorem poisson_inner_eq_integral (f g : Lp ℝ 2 μ) :
    inner ℝ f g = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- The scalar Dirichlet functional evaluated on a value–gradient pair. -/
def poissonEnergy {W : Type*} [NormedAddCommGroup W]
    (F f : Lp ℝ 2 μ) (g : Lp W 2 μ) : ℝ :=
  ∫ x, ‖g x‖ ^ 2 - 2 * f x * (F x - ∫ y, F y ∂μ) ∂μ

/-- The functional `poissonEnergy` has an integrable integrand for every `L²` jet. -/
theorem poissonEnergy_integrable {W : Type*} [NormedAddCommGroup W]
    (F f : Lp ℝ 2 μ) (g : Lp W 2 μ) :
    Integrable (fun x => ‖g x‖ ^ 2 - 2 * f x * (F x - ∫ y, F y ∂μ)) μ := by
  have hc : MemLp (fun x => F x - ∫ y, F y ∂μ) 2 μ :=
    (Lp.memLp F).sub (memLp_const _)
  have hp : Integrable (fun x => f x * (F x - ∫ y, F y ∂μ)) μ :=
    (Lp.memLp f).integrable_mul hc
  convert (Lp.memLp g).norm.integrable_sq.sub (hp.const_mul 2) using 1
  ext x
  simp only [Pi.sub_apply]
  ring

/-- Integral and Hilbert-space forms of the Dirichlet functional coincide. -/
theorem poissonEnergy_eq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (F f : Lp ℝ 2 μ) (g : Lp W 2 μ) :
    poissonEnergy μ F f g = ‖g‖ ^ 2 - 2 * inner ℝ (poissonCenter μ F) f := by
  have hprod : Integrable (fun x => poissonCenter μ F x * f x) μ :=
    (Lp.memLp (poissonCenter μ F)).integrable_mul (Lp.memLp f)
  have he : poissonEnergy μ F f g =
      ∫ x, ‖g x‖ ^ 2 - 2 * (poissonCenter μ F x * f x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [poissonCenter_ae μ F] with x hx
    rw [hx]
    ring
  have hn : (∫ x, ‖g x‖ ^ 2 ∂μ) = ‖g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hi : (∫ x, poissonCenter μ F x * f x ∂μ) = inner ℝ (poissonCenter μ F) f := by
    rw [L2.inner_def]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [he, integral_sub (Lp.memLp g).norm.integrable_sq (hprod.const_mul 2),
    integral_const_mul, hn, hi]

namespace Internal

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The general probability-space existence step. All hypotheses describe
its Hilbert-space realization and Poincaré bound. -/
theorem probability_poisson_exists
    (J : V →L[ℝ] Lp ℝ 2 μ) (G : V →L[ℝ] W) (e : V)
    (he : J e = Lp.const 2 μ (1 : ℝ)) (hGe : G e = 0)
    (hnorm : ∀ v, ‖v‖ ^ 2 = ‖J v‖ ^ 2 + ‖G v‖ ^ 2)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ v, ‖J v‖ ^ 2 - (poissonMean μ (J v)) ^ 2 ≤ C * ‖G v‖ ^ 2)
    (F : Lp ℝ 2 μ) :
    ∃ u : V, poissonMean μ (J u) = 0 ∧
      ∀ v, inner ℝ (G u) (G v) = inner ℝ (poissonCenter μ F) (J v) := by
  let M := (poissonMean μ).comp J
  apply exists_meanZero_poisson M G e
      (by simp [M, he, poissonMean_one]) hGe (C + 1) (by linarith)
      (fun v hv => ?_) ((innerSL ℝ (poissonCenter μ F)).comp J)
      (by
        change inner ℝ (poissonCenter μ F) (J e) = 0
        rw [he, real_inner_comm]
        exact poissonMean_center μ F)
  have hp := hP v
  change poissonMean μ (J v) = 0 at hv
  rw [hv, zero_pow (by norm_num), sub_zero] at hp
  rw [hnorm]
  nlinarith

omit [CompleteSpace V] in
/-- The Poincaré norm estimate on the mean-zero Sobolev subspace. -/
theorem probability_poisson_bound
    (J : V →L[ℝ] Lp ℝ 2 μ) (G : V →L[ℝ] W)
    (hnorm : ∀ v, ‖v‖ ^ 2 = ‖J v‖ ^ 2 + ‖G v‖ ^ 2)
    (C : ℝ)
    (hP : ∀ v, ‖J v‖ ^ 2 - (poissonMean μ (J v)) ^ 2 ≤ C * ‖G v‖ ^ 2)
    (v : V) (hv : ((poissonMean μ).comp J) v = 0) :
    ‖v‖ ^ 2 ≤ (C + 1) * ‖G v‖ ^ 2 := by
  have hp := hP v
  change poissonMean μ (J v) = 0 at hv
  rw [hv, zero_pow (by norm_num), sub_zero] at hp
  rw [hnorm]
  nlinarith

/-- Existence, uniqueness after centering, the affine solution set and the
variational characterization, for a Sobolev realization of a probability. -/
theorem probability_poisson
    (J : V →L[ℝ] Lp ℝ 2 μ) (G : V →L[ℝ] W) (e : V)
    (he : J e = Lp.const 2 μ (1 : ℝ)) (hGe : G e = 0)
    (hnorm : ∀ v, ‖v‖ ^ 2 = ‖J v‖ ^ 2 + ‖G v‖ ^ 2)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ v, ‖J v‖ ^ 2 - (poissonMean μ (J v)) ^ 2 ≤ C * ‖G v‖ ^ 2)
    (F : Lp ℝ 2 μ) :
    ∃ u : V, poissonMean μ (J u) = 0 ∧
      (∀ v, inner ℝ (G u) (G v) = inner ℝ (poissonCenter μ F) (J v)) ∧
      (∀ v, poissonMean μ (J v) = 0 →
        (∀ w, inner ℝ (G v) (G w) = inner ℝ (poissonCenter μ F) (J w)) → v = u) ∧
      (∀ v, (∀ w, inner ℝ (G v) (G w) = inner ℝ (poissonCenter μ F) (J w)) ↔
        ∃ a : ℝ, v = u + a • e) ∧
      (∀ v, (∀ w, ‖G v‖ ^ 2 - 2 * inner ℝ (poissonCenter μ F) (J v) ≤
          ‖G w‖ ^ 2 - 2 * inner ℝ (poissonCenter μ F) (J w)) ↔
        (∀ w, inner ℝ (G v) (G w) = inner ℝ (poissonCenter μ F) (J w))) := by
  obtain ⟨u, hmu, hu⟩ := probability_poisson_exists μ J G e he hGe hnorm C hC hP F
  let M := (poissonMean μ).comp J
  let ℓ := (innerSL ℝ (poissonCenter μ F)).comp J
  have hMe : M e = 1 := by simp [M, he, poissonMean_one]
  have hchar := poisson_solutions_iff M G e hMe hGe (C + 1)
    (probability_poisson_bound μ J G hnorm C hP) ℓ hu
  refine ⟨u, hmu, hu, ?_, hchar, poisson_minimizer_iff G ℓ hu⟩
  intro v hmv hv
  obtain ⟨a, rfl⟩ := (hchar v).mp hv
  have ha : a = 0 := by
    simpa [map_add, map_smul, he, hmu, poissonMean_one] using hmv
  simp [ha]

end Internal

end Riesz1

end
