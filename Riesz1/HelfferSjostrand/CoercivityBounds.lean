/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Coercivity
public import Riesz1.ToMathlib.L2CoordinateNorm

/-!
# Coercivity of the normalized full vector form

Part of the proof of Proposition 3.2: scalar Poincaré bounds the
component variances. The Hessian controls the squared differences of component
means, and the normalization makes their pair sum equal to `N` times their
squared norm. The argument applies directly to the completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The squared `L²` norm of the vector of component values. -/
def hsVectorValueNormSq (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (u : HsVectorJet μ) : ℝ := ∑ i, ‖hsJetValue μ i u‖ ^ 2

/-- The scalar gradient contribution to the vector form. -/
def hsVectorGradientNormSq (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (u : HsVectorJet μ) : ℝ :=
  ∑ i : Fin (N : ℕ), ‖hsSobolevGradient μ (u.ofLp.1 i)‖ ^ 2

theorem hsVectorSobolevForm_self (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorSobolev χ hN hc μ) :
    hsVectorSobolevForm χ hN hc μ u u =
      hsVectorGradientNormSq μ u.val + ‖u.val.ofLp.2‖ ^ 2 := by
  simp only [hsVectorSobolevForm, real_inner_self_eq_norm_sq, hsVectorGradientNormSq]

theorem hsEnergyWeight_sq_lower (χ : HsPairPotentials N c) (hc : 0 < c)
    (p : HsPairIndex N) {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    2 * c ≤ hsEnergyWeight χ p x ^ 2 := by
  have h := χ.curvature p.1.1 p.1.2 p.2 _ (hsChamber_separation_mem hx p.2)
  have hn : 0 ≤ 2 * deriv (deriv (χ.potential p.1.1 p.1.2)) (x p.1.2 - x p.1.1) := by
    linarith only [h, hc]
  rw [hsEnergyWeight, Real.sq_sqrt hn]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- Each pair energy controls the corresponding difference of scalar values. -/
theorem hsVector_pair_value_bound (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorSobolev χ hN hc μ)
    (p : HsPairIndex N) :
    2 * c * ‖hsJetValue μ p.1.2 u.val - hsJetValue μ p.1.1 u.val‖ ^ 2 ≤
      ‖hsJetEnergy μ p u.val‖ ^ 2 := by
  rw [poisson_norm_sq μ (hsJetValue μ p.1.2 u.val - hsJetValue μ p.1.1 u.val),
    poisson_norm_sq μ (hsJetEnergy μ p u.val), ← integral_const_mul]
  apply integral_mono_ae ((Lp.memLp _).integrable_sq.const_mul _) (Lp.memLp _).integrable_sq
  filter_upwards [hsVectorSobolev_energy_ae χ hN hc μ u p,
    Lp.coeFn_sub (hsJetValue μ p.1.2 u.val) (hsJetValue μ p.1.1 u.val)] with y he hd
  rw [he, hd]
  dsimp only [Pi.sub_apply]
  simp only [mul_pow]
  exact mul_le_mul_of_nonneg_right
    (hsEnergyWeight_sq_lower χ hc p (hsLiftPoint_mem_chamber N y)) (sq_nonneg _)

/-- All pair energies together control all pair differences in `L²`. -/
theorem hsVector_pair_sum_bound (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorSobolev χ hN hc μ) :
    2 * c * (∑ p : HsPairIndex N,
      ‖hsJetValue μ p.1.2 u.val - hsJetValue μ p.1.1 u.val‖ ^ 2) ≤ ‖u.val.ofLp.2‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum fun p _ => hsVector_pair_value_bound χ hN hc μ u p).trans_eq
    (sum_norm_sq_l2_coordinates μ u.val.ofLp.2)

namespace Internal

theorem hsVector_mean_sq_le (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]
    (v : Lp ℝ 2 μ) : (poissonMean μ v) ^ 2 ≤ ‖v‖ ^ 2 := by
  have h := integral_nonneg (μ := μ) (fun x => sq_nonneg (v x - ∫ y, v y ∂μ))
  rw [poisson_variance_eq] at h
  linarith

end Internal

/-- The component means of a normalized field are controlled by its Hessian energy. -/
theorem hsVector_mean_bound (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (u : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure _))
    (hu : ∑ i, poissonMean _ (hsJetValue _ i u.val) = 0) :
    (∑ i, (poissonMean _ (hsJetValue _ i u.val)) ^ 2) ≤
      (2 * c * (N : ℝ))⁻¹ * ‖u.val.ofLp.2‖ ^ 2 := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let m : Fin (N : ℕ) → ℝ := fun i => poissonMean μ (hsJetValue μ i u.val)
  have hm : ∑ i, m i = 0 := hu
  have hp : (∑ p : HsPairIndex N, (m p.1.2 - m p.1.1) ^ 2) =
      (N : ℝ) * ∑ i, m i ^ 2 := by
    rw [sum_hsPairIndex (fun i j => (m j - m i) ^ 2), sum_filter_lt_sq_eq, hm]
    ring
  have hmean : (∑ p : HsPairIndex N, (m p.1.2 - m p.1.1) ^ 2) ≤
      ∑ p : HsPairIndex N, ‖hsJetValue μ p.1.2 u.val - hsJetValue μ p.1.1 u.val‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro p _
    have h := Internal.hsVector_mean_sq_le μ
      (hsJetValue μ p.1.2 u.val - hsJetValue μ p.1.1 u.val)
    simpa only [map_sub] using h
  have hb := hsVector_pair_sum_bound χ hN hc μ u
  have hle := (mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤ 2 * c)).trans hb
  rw [hp] at hle
  apply (le_inv_mul_iff₀ (by positivity : 0 < 2 * c * (N : ℝ))).mpr
  nlinarith

theorem hsScalar_poincare_norm (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    ‖hsSobolevValue _ f‖ ^ 2 - (poissonMean _ (hsSobolevValue _ f)) ^ 2 ≤
      hsPoincareConstant N c * ‖hsSobolevGradient _ f‖ ^ 2 := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  have h := scalar_poincare_gibbs hPL hN χ hc f
  dsimp only at h
  rw [poisson_variance_eq] at h
  have hg : (∫ x, ‖hsSobolevGradient μ f x‖ ^ 2 ∂μ) = ‖hsSobolevGradient μ f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hg] at h
  exact h

theorem hsVector_variance_bound (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (u : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure _)) :
    hsVectorValueNormSq _ u.val - (∑ i, (poissonMean _ (hsJetValue _ i u.val)) ^ 2) ≤
      hsPoincareConstant N c * hsVectorGradientNormSq _ u.val := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  have hs : (∑ i : Fin (N : ℕ),
      (‖hsJetValue μ i u.val‖ ^ 2 - (poissonMean μ (hsJetValue μ i u.val)) ^ 2)) ≤
      ∑ i : Fin (N : ℕ),
        hsPoincareConstant N c * ‖hsSobolevGradient μ (u.val.ofLp.1 i)‖ ^ 2 :=
    Finset.sum_le_sum (fun i _ => hsScalar_poincare_norm hPL χ hN hc (u.val.ofLp.1 i))
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum,
    hsVectorValueNormSq, hsVectorGradientNormSq] using hs

/-- Full coercivity, with exactly the scalar Poincaré constant. -/
theorem hsVector_normalized_coercivity (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (u : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure _))
    (hu : ∑ i, poissonMean _ (hsJetValue _ i u.val) = 0) :
    hsVectorValueNormSq _ u.val ≤
      hsPoincareConstant N c * hsVectorSobolevForm χ hN hc _ u u := by
  have hs := hsVector_variance_bound hPL χ hN hc u
  have hm := hsVector_mean_bound χ hN hc u hu
  have hC : (2 * c * (N : ℝ))⁻¹ ≤ hsPoincareConstant N c := le_max_right _ _
  have hM := hm.trans (mul_le_mul_of_nonneg_right hC (sq_nonneg ‖u.val.ofLp.2‖))
  rw [hsVectorSobolevForm_self]
  rw [mul_add]
  linarith only [hs, hM]

end Riesz1
