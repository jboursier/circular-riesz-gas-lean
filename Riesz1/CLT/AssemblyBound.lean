/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SmoothingStatistics
public import Riesz1.CLT.VaryingLimit
public import Riesz1.CLT.NondegeneracyRegularized
public import Riesz1.ToMathlib.CircleSobolevTriangle

/-!
# Bounded-Lipschitz bounds for the central limit theorem assembly

General distance estimates used by the assembly `Riesz1/CLT/AssemblyDistance.lean`:

* a bounded-Lipschitz distance is at most `B` as soon as every test integral differs by at most
  `B` (`blDistance_le_of_forall_blTest`), applied to laws of random variables on a probability
  space (`blDistance_map_le`) and to the centred Gaussian laws (`blDistance_map_le_gaussian`).
* the standard deviations of two centred Gaussians compare by `blDistance_gaussianReal_le`.
* the square root of `cltVariance` satisfies the triangle inequality in its profile argument
  (`cltVariance_sqrt_sub_le`), which compares `σ_reg` with `σ_{ℓ_N}` in Theorem 3.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- A bounded-Lipschitz test is `1`-Lipschitz. -/
lemma blTest_lipschitz {f : ℝ → ℝ} (hf : BLTest f) : LipschitzWith 1 f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  exact abs_sub_le_of_blTest hf x y

/-- A bound on every bounded-Lipschitz test integral bounds the distance. -/
lemma blDistance_le_of_forall_blTest {μ ν : ProbabilityMeasure ℝ} {B : ℝ}
    (h : ∀ f : ℝ → ℝ, BLTest f → |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ B) :
    blDistance μ ν ≤ ENNReal.ofReal B :=
  iSup_le fun f => ENNReal.ofReal_le_ofReal (h f.val f.property)

/-- Laws of two random variables on a probability space: a bound on the test integrals of the
two images bounds the bounded-Lipschitz distance of the laws. -/
lemma blDistance_map_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F G : Ω → ℝ} (hF : AEMeasurable F μ) (hG : AEMeasurable G μ) {B : ℝ}
    (h : ∀ f : ℝ → ℝ, BLTest f → |(∫ X, f (F X) ∂μ) - ∫ X, f (G X) ∂μ| ≤ B) :
    blDistance ⟨μ.map F, inferInstance⟩ ⟨μ.map G, inferInstance⟩ ≤
      ENNReal.ofReal B := by
  refine blDistance_le_of_forall_blTest fun f hf => ?_
  show |(∫ x, f x ∂(μ.map F)) - ∫ x, f x ∂(μ.map G)| ≤ B
  rw [integral_map hF (hf.1.continuous.aestronglyMeasurable),
    integral_map hG (hf.1.continuous.aestronglyMeasurable)]
  exact h f hf

/-- The image of a random variable compared with a centred Gaussian of standard deviation `σ`:
a bound on the Stein-type test integrals bounds the bounded-Lipschitz distance. -/
lemma blDistance_map_le_gaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {G : Ω → ℝ} (hG : AEMeasurable G μ) (σ : ℝ≥0) {B : ℝ}
    (h : ∀ f : ℝ → ℝ, BLTest f →
      |(∫ X, f (G X) ∂μ) - ∫ z, f ((σ : ℝ) * z) ∂(gaussianReal 0 1)| ≤ B) :
    blDistance ⟨μ.map G, inferInstance⟩
      ⟨gaussianReal 0 (σ ^ 2), inferInstance⟩ ≤ ENNReal.ofReal B := by
  refine blDistance_le_of_forall_blTest fun f hf => ?_
  show |(∫ x, f x ∂(μ.map G)) - ∫ x, f x ∂(gaussianReal 0 (σ ^ 2))| ≤ B
  rw [integral_map hG (hf.1.continuous.aestronglyMeasurable), gaussianReal_zero_sq_eq_map,
    integral_map (measurable_const_mul (σ : ℝ)).aemeasurable
      (hf.1.continuous.aestronglyMeasurable)]
  exact h f hf

/-- The square root of `cltVariance` is a seminorm up to the constant `√κ`, and so satisfies the
reverse triangle inequality for finite profiles: `|√‖f‖ - √‖g‖| ≤ √‖f - g‖`. -/
theorem cltVariance_sqrt_sub_le (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (f g : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
    (hf : cltVariance P ℓ f ≠ ⊤) (hg : cltVariance P ℓ g ≠ ⊤)
    (he : cltVariance P ℓ (subL2 f g) ≠ ⊤) :
    |Real.sqrt (cltVariance P ℓ f).toReal - Real.sqrt (cltVariance P ℓ g).toReal| ≤
      Real.sqrt (cltVariance P ℓ (subL2 f g)).toReal := by
  set κ : ℝ := (2 * Real.pi) ^ (1 - P.val.2) /
    (2 * P.val.1 * rieszConstant (parametersExponent P)) * ℓ.val ^ (-P.val.2) with hκ
  have hκpos : 0 < κ := by
    have hβ : 0 < P.val.1 := P.property.1
    have hR : 0 < rieszConstant (parametersExponent P) := rieszConstant_pos _
    rw [hκ]
    exact mul_pos (div_pos (Real.rpow_pos_of_pos (by positivity) _)
      (mul_pos (mul_pos two_pos hβ) hR)) (Real.rpow_pos_of_pos ℓ.property.1 _)
  have hvar : ∀ h : {h : UnitAddCircle → ℂ // MemLp h 2 volume},
      (cltVariance P ℓ h).toReal = κ * (circleSobolevSq ((1 - P.val.2) / 2) h).toReal := by
    intro h
    rw [cltVariance, ENNReal.toReal_mul, ENNReal.toReal_ofReal hκpos.le]
  -- A finite prefactor makes the seminorm finite, since `κ > 0`.
  have hfin : ∀ h : {h : UnitAddCircle → ℂ // MemLp h 2 volume},
      cltVariance P ℓ h ≠ ⊤ → circleSobolevSq ((1 - P.val.2) / 2) h ≠ ⊤ := by
    intro h hh hS
    apply hh
    rw [cltVariance, hS, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hκpos).ne']
  have hκnn : 0 ≤ κ := hκpos.le
  rw [hvar f, hvar g, hvar (subL2 f g), Real.sqrt_mul hκnn, Real.sqrt_mul hκnn,
    Real.sqrt_mul hκnn, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ)]
  exact mul_le_mul_of_nonneg_left
    (circleSobolevSq_sqrt_sub_le ((1 - P.val.2) / 2) f g (hfin f hf) (hfin g hg) (hfin _ he))
    (Real.sqrt_nonneg κ)

/-- Where a random variable vanishes almost surely and the Gaussian variance is zero, the two
laws coincide, so their bounded-Lipschitz distance is zero. -/
lemma blDistance_map_eq_zero_of_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {G : Ω → ℝ} (hz : G =ᵐ[μ] fun _ => 0)
    (v : ℝ≥0) (hv : v = 0) :
    blDistance ⟨μ.map G, inferInstance⟩
      ⟨gaussianReal 0 v, inferInstance⟩ = 0 := by
  have hlaw : (⟨μ.map G, inferInstance⟩ : ProbabilityMeasure ℝ) =
      ⟨gaussianReal 0 v, inferInstance⟩ := by
    apply Subtype.ext
    show μ.map G = gaussianReal 0 v
    rw [Measure.map_congr hz, hv, gaussianReal_zero_var, Measure.map_const]
    simp
  rw [hlaw]
  exact blDistance_self _

end Riesz1

end
end
