/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Stein.Ross
public import Riesz1.ToMathlib.Stein.Uniqueness

/-!
# The bounded Gaussian Stein solution and its rescaling

The integrating-factor solution solves the equation of variance `σ²`. Its standardization is
`v(y) = σ u(σ y)`. Ross's estimates applied to the test `h(y) = f(σ y)` give `|u| ≤ 2` and
`|u'| ≤ √(2/π)/σ`. Bounded differentiable solutions are unique.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace Riesz1

/-- The Gaussian Stein equation follows by differentiating the integrating-factor formula. -/
lemma stein_ode {σ x : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hf' : ∀ y, |deriv f y| ≤ 1) :
    σ ^ 2 * deriv (steinSolution σ f) x - x * steinSolution σ f x =
      f x - ∫ z, f (σ * z) ∂(gaussianReal 0 1) := by
  have hd := (Internal.stein_hasDerivAt_formula hσ hf.continuous
    (Internal.ross_growth (L := 1) (fun a b => by
      simpa using Internal.ross_lipschitz hf hf' a b)) x).deriv
  have hs : σ ^ 2 ≠ 0 := by positivity
  rw [eq_div_iff hs] at hd
  linarith

/-- The integrating-factor solution is continuously differentiable. -/
lemma stein_contDiff_solution {σ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hf' : ∀ y, |deriv f y| ≤ 1) : ContDiff ℝ 1 (steinSolution σ f) := by
  have hb : ∀ y, |f y| ≤ |f 0| + 1 * |y| := Internal.ross_growth
    (fun a b => by simpa using Internal.ross_lipschitz hf hf' a b)
  have hd := Internal.stein_hasDerivAt_formula hσ hf.continuous hb
  refine contDiff_one_iff_deriv.2 ⟨fun x => (hd x).differentiableAt, ?_⟩
  have he : deriv (steinSolution σ f) = fun x =>
      (x * steinSolution σ f x + f x - ∫ z, f (σ * z) ∂(gaussianReal 0 1)) / σ ^ 2 :=
    funext fun x => (hd x).deriv
  rw [he]
  have hdiff : Differentiable ℝ (steinSolution σ f) := fun x => (hd x).differentiableAt
  have hc : Continuous (steinSolution σ f) := hdiff.continuous
  fun_prop

namespace Internal

/-- Standardizing the integrating-factor solution gives the standard Stein solution. -/
lemma stein_standardize {σ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hf' : ∀ y, |deriv f y| ≤ 1) :
    (fun y => σ * steinSolution σ f (σ * y)) = steinSolution 1 (fun y => f (σ * y)) := by
  let h := fun y => f (σ * y)
  have hLip : ∀ a b, |h a - h b| ≤ σ * |a - b| := by
    intro a b
    refine (ross_lipschitz hf hf' (σ * a) (σ * b)).trans_eq ?_
    rw [← mul_sub, abs_mul, abs_of_pos hσ]
  have hc : Continuous h := by dsimp [h]; fun_prop
  have hV := stein_hasDerivAt_formula zero_lt_one hc (ross_growth hLip)
  let V := steinSolution 1 h
  let w := fun x => σ⁻¹ * V (x / σ)
  have hw : ∀ x, HasDerivAt w (σ⁻¹ * (deriv V (x / σ) / σ)) x := by
    intro x
    have hd := ((hV (x / σ)).comp x ((hasDerivAt_id' x).div_const σ)).const_mul σ⁻¹
    exact hd.congr_deriv (by rw [(hV (x / σ)).deriv]; ring)
  have hwb : ∀ x, |w x| ≤ 1 := by
    intro x
    dsimp [w, V]
    rw [abs_mul, abs_of_pos (inv_pos.2 hσ)]
    calc σ⁻¹ * |steinSolution 1 h (x / σ)| ≤ σ⁻¹ * σ :=
        mul_le_mul_of_nonneg_left (ross_formula_bounds hσ.le hLip _).1 (inv_nonneg.2 hσ.le)
      _ = 1 := inv_mul_cancel₀ hσ.ne'
  have he : ∀ x, σ ^ 2 * deriv w x - x * w x =
      f x - ∫ z, f (σ * z) ∂(gaussianReal 0 1) := by
    intro x
    have hode := (hV (x / σ)).deriv
    simp only [one_pow, one_mul, div_one] at hode
    have hh : h (x / σ) = f x := by dsimp [h]; congr 1; field_simp
    rw [hh] at hode
    rw [(hw x).deriv]
    dsimp [w]
    change σ ^ 2 * (σ⁻¹ * (deriv V (x / σ) / σ)) - x * (σ⁻¹ * V (x / σ)) = _
    field_simp at hode ⊢
    linear_combination hode
  have hg : ∀ y, |f y| ≤ |f 0| + 1 * |y| := ross_growth
    (fun a b => by simpa using ross_lipschitz hf hf' a b)
  have hwEq := stein_eq_formula hσ hf.continuous hg (fun x => (hw x).differentiableAt) ⟨1, hwb⟩ he
  funext y
  have ht := congrFun hwEq (σ * y)
  dsimp [w] at ht
  have hy : σ * y / σ = y := by field_simp
  rw [hy] at ht
  change σ * steinSolution σ f (σ * y) = V y
  rw [← ht]
  field_simp

end Internal

/-- Ross's standard bounds applied to `v(y) = σ u(σ y)`, followed by rescaling. -/
lemma stein_solution_bounds {σ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hf' : ∀ y, |deriv f y| ≤ 1) :
    (∀ x, |steinSolution σ f x| ≤ 2) ∧
      (∀ x, |deriv (steinSolution σ f) x| ≤ √(2 / π) / σ) := by
  let h := fun y => f (σ * y)
  let v := fun y => σ * steinSolution σ f (σ * y)
  have hu := stein_contDiff_solution hf hσ hf'
  have hh : ContDiff ℝ 1 h := hf.comp (contDiff_const.mul contDiff_id)
  have hh' : ∀ y, HasDerivAt h (σ * deriv f (σ * y)) y := by
    intro y
    exact (((hf.differentiable one_ne_zero _).hasDerivAt).comp y
      ((hasDerivAt_id' y).const_mul σ)).congr_deriv (by ring)
  have hdb : ∀ y, |deriv h y| ≤ σ := by
    intro y
    rw [(hh' y).deriv, abs_mul, abs_of_pos hσ]
    exact mul_le_of_le_one_right hσ.le (hf' _)
  have hv : ∀ y, HasDerivAt v (σ ^ 2 * deriv (steinSolution σ f) (σ * y)) y := by
    intro y
    exact (((hu.differentiable one_ne_zero _).hasDerivAt.comp y
      ((hasDerivAt_id' y).const_mul σ)).const_mul σ).congr_deriv (by ring)
  have hvEq : v = steinSolution 1 h := Internal.stein_standardize hf hσ hf'
  have hLip : ∀ a b, |h a - h b| ≤ σ * |a - b| := by
    intro a b
    have hb := Internal.ross_lipschitz hf hf' (σ * a) (σ * b)
    simpa only [h, ← mul_sub, abs_mul, abs_of_pos hσ] using hb
  have hvb : ∃ C, ∀ y, |v y| ≤ C := by
    rw [hvEq]
    exact ⟨σ, fun y => (Internal.ross_formula_bounds hσ.le hLip y).1⟩
  have hve : ∀ y, deriv v y - y * v y = h y - ∫ z, h z ∂(gaussianReal 0 1) := by
    intro y
    rw [hvEq]
    have hd := (Internal.stein_hasDerivAt_formula zero_lt_one hh.continuous
      (Internal.ross_growth hLip) y).deriv
    simp only [one_pow, one_mul, div_one] at hd
    linarith
  obtain ⟨hvb', hvd'⟩ := ross_lemma_2_5_part_2 h
    (fun a b => hh.contDiffOn.absolutelyContinuousOnInterval) σ hσ.le
    (Eventually.of_forall hdb) v (fun y => (hv y).differentiableAt) hvb hve
  have hy : ∀ x : ℝ, σ * (x / σ) = x := fun x => by field_simp
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hb := hvb' (x / σ)
    dsimp [v] at hb
    rw [hy, abs_mul, abs_of_pos hσ] at hb
    nlinarith
  · have hb := hvd' (x / σ)
    rw [(hv (x / σ)).deriv, hy, abs_mul, abs_of_nonneg (sq_nonneg σ)] at hb
    rw [le_div_iff₀ hσ]
    nlinarith

/-- The integrating-factor solution is the unique bounded differentiable Stein solution. -/
theorem stein_bounded_solution {σ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hσ : 0 < σ)
    (hf' : ∀ y, |deriv f y| ≤ 1) :
    ContDiff ℝ 1 (steinSolution σ f) ∧ (∃ C, ∀ x, |steinSolution σ f x| ≤ C) ∧
      ∀ u : ℝ → ℝ, Differentiable ℝ u → (∃ C, ∀ x, |u x| ≤ C) →
        (∀ x, σ ^ 2 * deriv u x - x * u x =
          f x - ∫ z, f (σ * z) ∂(gaussianReal 0 1)) → u = steinSolution σ f := by
  have hu := stein_contDiff_solution hf hσ hf'
  have hb : ∃ C, ∀ x, |steinSolution σ f x| ≤ C := ⟨2, (stein_solution_bounds hf hσ hf').1⟩
  exact ⟨hu, hb, fun u hd hub he => stein_solution_unique σ hσ _ u (steinSolution σ f)
    hd (hu.differentiable one_ne_zero) hub hb he (fun _ => stein_ode hf hσ hf')⟩

end Riesz1
