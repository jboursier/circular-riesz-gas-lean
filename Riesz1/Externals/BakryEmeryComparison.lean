/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Externals.BakryEmeryNormalization
public import Riesz1.ToMathlib.PrekopaWholeSpace
public import Riesz1.ToMathlib.Gaussian.DensityLimit

/-!
# Interpolation estimates toward Bakry–Émery

The pointwise majorant below is the quadratic optimization in the Prékopa–Leindler
approach of Bobkov–Ledoux, *From Brunn–Minkowski to Brascamp–Lieb and to logarithmic
Sobolev inequalities*, GAFA 10 (2000), Proposition 3.1, pp. 1034–1035.
https://www.math.univ-toulouse.fr/~ledoux/BrunnMinkowski.pdf
The proofs here are original Lean code. No external code is ported.

We also obtain whole-space normalized midpoint integral comparisons from the
midpoint Prékopa–Leindler hypothesis. These are intermediate results toward
the Bakry–Émery criterion. The entropy inequality is not established here.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff InnerProductSpace

namespace Riesz1.Externals

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {V g : E → ℝ} {κ M s t : ℝ}

omit [CompleteSpace E] in
/-- The curvature defect at any interpolation weight. -/
theorem bakry_emery_weighted_curvature (hV : ContDiff ℝ 2 V)
    (hH : ∀ x h, κ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) (x y : E) :
    κ / 2 * t * s * ‖x - y‖ ^ 2 ≤
      t * V x + s * V y - V (t • x + s • y) := by
  have hc := strongConvexOn_of_hessian_lower convex_univ isOpen_univ hV.contDiffOn
    (fun z _ h => hH z h)
  have hi := hc.2 (mem_univ x) (mem_univ y) ht hs hts
  dsimp only [smul_eq_mul] at hi
  linarith

/-- A global bound for the interpolating exponent, with the sharp coefficient as `s → 0`.
The denominator is used only with a positivity certificate. -/
theorem bakry_emery_interpolation_majorant (hV : ContDiff ℝ 2 V)
    (hH : ∀ x h, κ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    (hg : ContDiff ℝ 2 g)
    (hgH : ∀ x h, (fderiv ℝ (fderiv ℝ g) x h) h ≤ M * ‖h‖ ^ 2)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) (hD : 0 < κ * t - M * s)
    (x y : E) :
    g x - (t * V x + s * V y - V (t • x + s • y)) ≤
      g (t • x + s • y) +
        s / (2 * (κ * t - M * s)) * ‖gradient g (t • x + s • y)‖ ^ 2 := by
  let z := t • x + s • y
  have hxz : x - z = s • (x - y) := by
    dsimp [z]
    have ht' : t = 1 - s := by linarith
    rw [ht']
    module
  have hTaylor := le_quadratic_tangent_of_hessian_upper convex_univ isOpen_univ
    hg.contDiffOn (fun z _ h => hgH z h) (mem_univ z) (mem_univ x)
  rw [hxz, map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg hs, mul_pow,
    ← inner_gradient_left] at hTaylor
  have hcurv := bakry_emery_weighted_curvature hV hH ht hs hts x y
  have hquad := mul_le_mul_of_nonneg_left
    (inner_sub_quadratic_le hD (gradient g z) (x - y)) hs
  change g x - (t * V x + s * V y - V z) ≤
    g z + s / (2 * (κ * t - M * s)) * ‖gradient g z‖ ^ 2
  have he : s * (‖gradient g z‖ ^ 2 / (2 * (κ * t - M * s))) =
      s / (2 * (κ * t - M * s)) * ‖gradient g z‖ ^ 2 := by ring
  rw [he] at hquad
  nlinarith

end Pointwise

variable {d : ℕ} {w : ℝ} {V : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Bounded continuous perturbations preserve integrability of the unnormalized density. -/
theorem bakry_emery_integrable_exp_perturbation (hw : 0 < w)
    (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    {A : EuclideanSpace ℝ (Fin d) → ℝ} (hA : Continuous A)
    (hbA : Bornology.IsBounded (range A)) :
    Integrable (fun x => Real.exp (-V x + A x)) volume := by
  obtain ⟨C, hC⟩ := hbA.exists_norm_le
  have hi := (bakry_emery_density_integrable hw hV hH).mul_bdd
    (g := fun x => Real.exp (A x)) (Real.continuous_exp.comp hA).aestronglyMeasurable
    (c := Real.exp C) (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hC _ (mem_range_self x))))
  simpa only [Real.exp_add] using hi

/-- Normalized midpoint integral comparison under the uniformly convex density.
The pointwise premise is an internal comparison assumption, not an LSI hypothesis. -/
theorem bakry_emery_midpoint_comparison (hPL : External.PrekopaLeindler) (hd : 0 < d)
    (hw : 0 < w) (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    {A B C : EuclideanSpace ℝ (Fin d) → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C)
    (hbA : Bornology.IsBounded (range A)) (hbB : Bornology.IsBounded (range B))
    (hbC : Bornology.IsBounded (range C))
    (hmid : ∀ x y, A x + B y ≤
      2 * C ((1 / 2 : ℝ) • (x + y)) + w⁻¹ / 4 * ‖x - y‖ ^ 2) :
    let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
    (∫ x, Real.exp (A x) ∂ν) * (∫ x, Real.exp (B x) ∂ν) ≤
      (∫ x, Real.exp (C x) ∂ν) ^ 2 := by
  have hi := prekopa_exp_integral hPL hd (hV.continuous.neg.add hA)
    (hV.continuous.neg.add hB) (hV.continuous.neg.add hC)
    (bakry_emery_integrable_exp_perturbation hw hV hH hA hbA)
    (bakry_emery_integrable_exp_perturbation hw hV hH hB hbB)
    (bakry_emery_integrable_exp_perturbation hw hV hH hC hbC) (by
      intro x y
      have hc := bakry_emery_weighted_curvature
        (hV.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) hH
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1) x y
      rw [← smul_add] at hc
      change (-V x + A x) + (-V y + B y) ≤
        2 * (-V ((1 / 2 : ℝ) • (x + y)) + C ((1 / 2 : ℝ) • (x + y)))
      linarith [hmid x y])
  have hZ := bakry_emery_normalization_pos hw hV hH
  have hden : ∀ x, 0 ≤ Real.exp (-V x) := fun _ => (Real.exp_pos _).le
  have hm : Measurable (fun x => Real.exp (-V x)) :=
    (Real.continuous_exp.comp hV.continuous.neg).measurable
  dsimp only
  rw [Gaussian.integral_normalized_density hm hden hZ,
    Gaussian.integral_normalized_density hm hden hZ,
    Gaussian.integral_normalized_density hm hden hZ]
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hi 2
  rw [Real.sq_sqrt (by positivity)] at hs
  simp_rw [Pi.add_apply, Pi.neg_apply, Real.exp_add] at hs
  have he := div_le_div_of_nonneg_right hs (sq_nonneg (∫ x, Real.exp (-V x)))
  simpa only [div_pow, div_mul_div_comm, pow_two] using he

end Riesz1.Externals

end
