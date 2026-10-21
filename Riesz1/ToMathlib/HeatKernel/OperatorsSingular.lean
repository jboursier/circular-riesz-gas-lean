/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HeatKernel.OperatorsHeat

/-!
# Singular integral formula for the fractional Laplacian on the unit circle

For a smooth `f` on the unit circle and `0 < γ < 1/2`,
`(-Δ)^γ f(x) = C_γ ∑_{n ∈ ℤ} ∫_0^1 (f(x) - f(y)) / |x - y - n|^{1+2γ} dy`, with
`C_γ = 2^{2γ} Γ(γ + 1/2) / (√π |Γ(-γ)|)`, and the double sum converges absolutely.

The proof starts from the positive-power formula of `OperatorsHeat`. The heat kernel is written as
a periodized Gaussian, the time integral is evaluated by Fubini and the Gamma substitution
`t ↦ 1/t`, and the resulting integral over `ℝ` is folded back into the sum over the translates
`x - y - n`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

open Complex (I)

/-- The Gaussian kernel `G_t(u) = (4πt)^{-1/2} e^{-u²/(4t)}`. For `t > 0` it is the heat kernel on
`ℝ`. Its values at `t ≤ 0` are never used. -/
noncomputable def gaussKernel (t u : ℝ) : ℝ :=
  (4 * π * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-u ^ 2 / (4 * t))

/-- The residual `f(x) - f(x - v)` of a function on the unit circle, as a function of `v`. -/
noncomputable def residualFun (f : UnitAddCircle → ℝ) (x v : ℝ) : ℝ :=
  f (x : UnitAddCircle) - f ((x - v : ℝ) : UnitAddCircle)

/-- The weight `(4π)^{-1/2} 2^{1+2γ} Γ(γ + 1/2)` of the time integral of `G_t(u) t^{-1-γ}`. -/
noncomputable def singularWeight (γ : ℝ) : ℝ :=
  (4 * π) ^ (-(1 / 2 : ℝ)) * 2 ^ (1 + 2 * γ) * Real.Gamma (γ + 1 / 2)

/-- The coefficient `C_γ = 2^{2γ} Γ(γ + 1/2) / (√π |Γ(-γ)|)` in the paper. -/
@[expose] noncomputable def singularConst (γ : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 * γ) * Real.Gamma (γ + 1 / 2) / (Real.sqrt π * |Real.Gamma (-γ)|)

/-! ### The Gaussian kernel -/

lemma gaussKernel_nonneg {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 ≤ gaussKernel t u :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

lemma gaussKernel_continuous {t : ℝ} (_ht : 0 < t) : Continuous (gaussKernel t) := by
  unfold gaussKernel
  exact continuous_const.mul (Real.continuous_exp.comp (by fun_prop))

lemma integrable_exp_div {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => Real.exp (-u ^ 2 / c)) := by
  refine (integrable_exp_neg_mul_sq (b := 1 / c) (by positivity)).congr
    (ae_of_all _ fun u => ?_)
  show Real.exp (-(1 / c) * u ^ 2) = Real.exp (-u ^ 2 / c)
  congr 1
  ring

lemma integral_exp_div {c : ℝ} (hc : 0 < c) :
    ∫ u : ℝ, Real.exp (-u ^ 2 / c) = √(π * c) := by
  have h := integral_gaussian (1 / c)
  have hc' : π / (1 / c) = π * c := by field_simp
  rw [hc'] at h
  rw [← h]
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun u => ?_)
  show Real.exp (-u ^ 2 / c) = Real.exp (-(1 / c) * u ^ 2)
  congr 1
  ring

lemma gaussKernel_integrable {t : ℝ} (ht : 0 < t) : Integrable (gaussKernel t) := by
  have h := (integrable_exp_div (c := 4 * t) (by positivity)).const_mul
    ((4 * π * t) ^ (-(1 / 2 : ℝ)))
  refine h.congr (ae_of_all _ fun u => ?_)
  unfold gaussKernel
  rfl

lemma integral_gaussKernel {t : ℝ} (ht : 0 < t) : ∫ u, gaussKernel t u = 1 := by
  have hpos : 0 < 4 * π * t := by positivity
  have h1 : ∫ u, gaussKernel t u = (4 * π * t) ^ (-(1 / 2 : ℝ)) * √(π * (4 * t)) := by
    rw [← integral_exp_div (c := 4 * t) (by positivity), ← MeasureTheory.integral_const_mul]
    rfl
  rw [h1, show π * (4 * t) = 4 * π * t by ring, Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
  norm_num

/-- The Gaussian first absolute moment: the integrand `|u| G_t(u)` is dominated by a multiple of
the Gaussian `e^{-u²/(8t)}`. -/
lemma abs_mul_gaussKernel_le {t : ℝ} (ht : 0 < t) (u : ℝ) :
    |u| * gaussKernel t u ≤
      (4 * π * t) ^ (-(1 / 2 : ℝ)) * (√(8 * t) / 2) * Real.exp (-u ^ 2 / (8 * t)) := by
  set r := √(8 * t) with hr_def
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr0 : r ≠ 0 := hr.ne'
  have hr2 : r ^ 2 = 8 * t := Real.sq_sqrt (by positivity)
  set w := |u| / r with hw_def
  have hw0 : 0 ≤ w := by positivity
  have hu : |u| = w * r := by rw [hw_def]; field_simp
  have hsq : u ^ 2 = (w ^ 2) * (8 * t) := by
    rw [← hr2, ← sq_abs u, hu]
    ring
  have e1 : -u ^ 2 / (4 * t) = -(2 * w ^ 2) := by
    rw [hsq]
    field_simp
    ring
  have e2 : -u ^ 2 / (8 * t) = -(w ^ 2) := by
    rw [hsq]
    field_simp
  have hexp : Real.exp (-(2 * w ^ 2)) = Real.exp (-(w ^ 2)) * Real.exp (-(w ^ 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have key : w * Real.exp (-(w ^ 2)) ≤ 1 / 2 := by
    have h1 : 2 * w ≤ Real.exp (w ^ 2) := by
      nlinarith [Real.add_one_le_exp (w ^ 2), sq_nonneg (w - 1)]
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith
  unfold gaussKernel
  rw [e1, e2, hexp, hu]
  have hq : 0 ≤ (4 * π * t) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hE : 0 ≤ Real.exp (-(w ^ 2)) := (Real.exp_pos _).le
  calc w * r * ((4 * π * t) ^ (-(1 / 2 : ℝ)) * (Real.exp (-(w ^ 2)) * Real.exp (-(w ^ 2))))
      = (4 * π * t) ^ (-(1 / 2 : ℝ)) * (r * Real.exp (-(w ^ 2))) * (w * Real.exp (-(w ^ 2))) := by
        ring
    _ ≤ (4 * π * t) ^ (-(1 / 2 : ℝ)) * (r * Real.exp (-(w ^ 2))) * (1 / 2) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hq (mul_nonneg hr.le hE))
    _ = (4 * π * t) ^ (-(1 / 2 : ℝ)) * (r / 2) * Real.exp (-(w ^ 2)) := by ring

lemma integrable_abs_mul_gaussKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ℝ => |u| * gaussKernel t u) := by
  have hdom : Integrable (fun u : ℝ =>
      (4 * π * t) ^ (-(1 / 2 : ℝ)) * (√(8 * t) / 2) * Real.exp (-u ^ 2 / (8 * t))) :=
    (integrable_exp_div (c := 8 * t) (by positivity)).const_mul _
  refine Integrable.mono' hdom
    ((continuous_abs.mul (gaussKernel_continuous ht)).aestronglyMeasurable)
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (gaussKernel_nonneg ht u)]
  exact abs_mul_gaussKernel_le ht u

/-- The value of the Gaussian moment bound, `(4πt)^{-1/2} (√(8t)/2) √(8πt) = 2√t`. -/
lemma gauss_moment_const {t : ℝ} (ht : 0 < t) :
    (4 * π * t) ^ (-(1 / 2 : ℝ)) * (√(8 * t) / 2) * √(π * (8 * t)) = 2 * √t := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hs1 : √(4 * π * t) = 2 * √π * √t := by
    rw [show 4 * π * t = 2 ^ 2 * (π * t) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num), Real.sqrt_mul hπ.le]
    ring
  have hs23 : √(8 * t) * √(π * (8 * t)) = 8 * t * √π := by
    rw [← Real.sqrt_mul (by positivity), show 8 * t * (π * (8 * t)) = (8 * t * √π) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hπ.le]; ring, Real.sqrt_sq (by positivity)]
  have hq : (4 * π * t) ^ (-(1 / 2 : ℝ)) = (2 * √π * √t)⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← hs1, Real.sqrt_eq_rpow]
  rw [hq]
  have hsq : √t * √t = t := Real.mul_self_sqrt ht.le
  have hsp : √π ≠ 0 := (Real.sqrt_pos.2 hπ).ne'
  have hst : √t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  calc (2 * √π * √t)⁻¹ * (√(8 * t) / 2) * √(π * (8 * t))
      = (2 * √π * √t)⁻¹ * (√(8 * t) * √(π * (8 * t))) / 2 := by ring
    _ = (2 * √π * √t)⁻¹ * (8 * t * √π) / 2 := by rw [hs23]
    _ = 2 * √t := by
      field_simp
      nlinarith [hsq]

/-- The first absolute moment of the Gaussian kernel is at most `2√t`. -/
lemma integral_abs_mul_gaussKernel_le {t : ℝ} (ht : 0 < t) :
    ∫ u, |u| * gaussKernel t u ≤ 2 * √t := by
  have hdom : Integrable (fun u : ℝ =>
      (4 * π * t) ^ (-(1 / 2 : ℝ)) * (√(8 * t) / 2) * Real.exp (-u ^ 2 / (8 * t))) :=
    (integrable_exp_div (c := 8 * t) (by positivity)).const_mul _
  calc ∫ u, |u| * gaussKernel t u
      ≤ ∫ u : ℝ, (4 * π * t) ^ (-(1 / 2 : ℝ)) * (√(8 * t) / 2) * Real.exp (-u ^ 2 / (8 * t)) :=
        integral_mono (integrable_abs_mul_gaussKernel ht) hdom (fun u => abs_mul_gaussKernel_le ht u)
    _ = (4 * π * t) ^ (-(1 / 2 : ℝ)) * (√(8 * t) / 2) * √(π * (8 * t)) := by
        rw [MeasureTheory.integral_const_mul, integral_exp_div (by positivity)]
    _ = 2 * √t := gauss_moment_const ht

/-! ### Unfolding a integral over `ℝ` into a sum over translates of `[0, 1]` -/

/-- Unfolding: the integrals of an integrable function over the translates `[n, n+1)` add up to
its integral over `ℝ`. -/
lemma hasSum_unfold_plus (ψ : ℝ → ℝ) (hψ : Integrable ψ) :
    HasSum (fun n : ℤ => ∫ y in (0 : ℝ)..1, ψ (y + n)) (∫ u, ψ u) := by
  have hm : ∀ n : ℤ, MeasurableSet (Ico (n : ℝ) (n + 1)) := fun n => measurableSet_Ico
  have hd : Pairwise (fun n m : ℤ => Disjoint (Ico (n : ℝ) (n + 1)) (Ico (m : ℝ) (m + 1))) := by
    intro n m hnm
    rcases lt_or_gt_of_ne hnm with h | h
    · exact Set.Ico_disjoint_Ico.2 (by
        rw [min_le_iff]; left; rw [le_max_iff]; right; exact_mod_cast (show n + 1 ≤ m by omega))
    · exact (Set.Ico_disjoint_Ico.2 (by
        rw [min_le_iff]; left; rw [le_max_iff]; right; exact_mod_cast (show m + 1 ≤ n by omega))).symm
  have hcov : ⋃ n : ℤ, Ico (n : ℝ) (n + 1) = univ := iUnion_Ico_intCast ℝ
  have h := hasSum_integral_iUnion (μ := volume) (f := ψ) hm hd
    (by rw [hcov]; exact hψ.integrableOn)
  rw [hcov, Measure.restrict_univ] at h
  convert h using 1
  funext n
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : (n : ℝ) ≤ n + 1)]
  rw [intervalIntegral.integral_comp_add_right ψ (n : ℝ)]
  simp only [zero_add, add_comm (1 : ℝ) (n : ℝ)]

/-- The same unfolding with translates `y - n`. -/
lemma hasSum_unfold_minus (ψ : ℝ → ℝ) (hψ : Integrable ψ) :
    HasSum (fun n : ℤ => ∫ y in (0 : ℝ)..1, ψ (y - n)) (∫ u, ψ u) := by
  have h := hasSum_unfold_plus ψ hψ
  rw [← (Equiv.neg ℤ).hasSum_iff] at h
  convert h using 1
  funext n
  simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg, sub_eq_add_neg]

/-- The lift of a function on the unit circle is invariant under integer translation. -/
lemma lift_add_int (f : UnitAddCircle → ℝ) (z : ℝ) (n : ℤ) :
    f ((z + n : ℝ) : UnitAddCircle) = f (z : UnitAddCircle) := by
  have h := (lift_periodic f).int_mul n z
  rw [mul_one] at h
  exact h

/-! ### The heat convolution as a Gaussian convolution on `ℝ` -/

lemma integrable_shift_mul_gauss (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    Integrable (fun v : ℝ => f ((x - v : ℝ) : UnitAddCircle) * gaussKernel t v) := by
  obtain ⟨M, hM⟩ := exists_bound_lift f hf
  have hfc : Continuous fun u : ℝ => f (u : UnitAddCircle) :=
    (show ContDiff ℝ ∞ (fun u : ℝ => f (u : UnitAddCircle)) from hf).continuous
  have hcomp : Continuous fun v : ℝ => f ((x - v : ℝ) : UnitAddCircle) :=
    hfc.comp (continuous_const.sub continuous_id)
  refine Integrable.mono' ((gaussKernel_integrable ht).const_mul M)
    (hcomp.mul (gaussKernel_continuous ht)).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussKernel_nonneg ht v)]
  exact mul_le_mul_of_nonneg_right (hM _) (gaussKernel_nonneg ht v)

/-- The heat convolution is the convolution with the Gaussian kernel over `ℝ`. -/
lemma heatConvolution_eq_gauss (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    heatConvolution f ht x = ∫ v, f ((x - v : ℝ) : UnitAddCircle) * gaussKernel t v := by
  obtain ⟨M, hM⟩ := exists_bound_lift f hf
  have hfc : Continuous fun u : ℝ => f (u : UnitAddCircle) :=
    (show ContDiff ℝ ∞ (fun u : ℝ => f (u : UnitAddCircle)) from hf).continuous
  have hcomp : Continuous fun y : ℝ => f ((x - y : ℝ) : UnitAddCircle) :=
    hfc.comp (continuous_const.sub continuous_id)
  have hW : ∀ y : ℝ, circleHeatKernel t ht y = ∑' n : ℤ, gaussKernel t (y - n) := by
    intro y
    rw [circleHeatKernel_eq_gauss t ht y, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rfl
  have hψ := integrable_shift_mul_gauss f hf ht x
  have hsumG : Summable (fun n : ℤ => ∫ y in Ioc (0 : ℝ) 1, gaussKernel t (y - n)) := by
    have h := hasSum_unfold_minus (gaussKernel t) (gaussKernel_integrable ht)
    simp only [intervalIntegral.integral_of_le zero_le_one] at h
    exact h.summable
  have hint : ∀ n : ℤ, Integrable (fun y : ℝ => f ((x - y : ℝ) : UnitAddCircle) *
      gaussKernel t (y - n)) (volume.restrict (Ioc 0 1)) := by
    intro n
    have hc : Continuous fun y : ℝ => f ((x - y : ℝ) : UnitAddCircle) * gaussKernel t (y - n) :=
      hcomp.mul ((gaussKernel_continuous ht).comp (continuous_id.sub continuous_const))
    exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hsum : Summable (fun n : ℤ => ∫ y in Ioc (0 : ℝ) 1,
      ‖f ((x - y : ℝ) : UnitAddCircle) * gaussKernel t (y - n)‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _)
      (fun n => ?_) (hsumG.mul_left M)
    have hGint : IntegrableOn (fun y : ℝ => M * gaussKernel t (y - n)) (Ioc 0 1) :=
      (((gaussKernel_integrable ht).comp_sub_right (n : ℝ)).const_mul M).integrableOn
    calc ∫ y in Ioc (0 : ℝ) 1, ‖f ((x - y : ℝ) : UnitAddCircle) * gaussKernel t (y - n)‖
        ≤ ∫ y in Ioc (0 : ℝ) 1, M * gaussKernel t (y - n) := by
          refine integral_mono (hint n).norm hGint (fun y => ?_)
          rw [norm_mul, Real.norm_of_nonneg (gaussKernel_nonneg ht _)]
          exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hM _)
            (gaussKernel_nonneg ht _)
      _ = M * ∫ y in Ioc (0 : ℝ) 1, gaussKernel t (y - n) := integral_const_mul _ _
  have hterm : ∀ n : ℤ, ∫ y in Ioc (0 : ℝ) 1, f ((x - y : ℝ) : UnitAddCircle) *
      gaussKernel t (y - n) = ∫ y in (0 : ℝ)..1,
        f ((x - (y - n) : ℝ) : UnitAddCircle) * gaussKernel t (y - n) := by
    intro n
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc (fun y _ => ?_)
    rw [show x - (y - n) = (x - y) + n by ring, lift_add_int f (x - y) n]
  have hval : ∫ y in (0 : ℝ)..1, f ((x - y : ℝ) : UnitAddCircle) * circleHeatKernel t ht y =
      ∫ v, f ((x - v : ℝ) : UnitAddCircle) * gaussKernel t v := by
    have hpt : ∀ y : ℝ, f ((x - y : ℝ) : UnitAddCircle) * circleHeatKernel t ht y =
        ∑' n : ℤ, f ((x - y : ℝ) : UnitAddCircle) * gaussKernel t (y - n) := by
      intro y
      rw [hW y, tsum_mul_left]
    rw [intervalIntegral.integral_of_le zero_le_one]
    simp only [hpt]
    rw [← integral_tsum_of_summable_integral_norm hint hsum]
    simp only [hterm]
    exact (hasSum_unfold_minus (fun v => f ((x - v : ℝ) : UnitAddCircle) * gaussKernel t v)
      hψ).tsum_eq
  unfold heatConvolution
  exact hval

/-- The heat residual is the Gaussian average of the residual `f(x) - f(x - v)`. -/
lemma heat_residual (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    f (x : UnitAddCircle) - heatConvolution f ht x =
      ∫ v, residualFun f x v * gaussKernel t v := by
  have h1 : ∫ v, f (x : UnitAddCircle) * gaussKernel t v = f (x : UnitAddCircle) := by
    rw [MeasureTheory.integral_const_mul, integral_gaussKernel ht, mul_one]
  rw [heatConvolution_eq_gauss f hf ht x, ← h1,
    ← integral_sub ((gaussKernel_integrable ht).const_mul _)
      (integrable_shift_mul_gauss f hf ht x)]
  congr 1
  funext v
  unfold residualFun
  ring

/-! ### Lipschitz bound of the residual -/

/-- The residual `f(x) - f(x - v)` is bounded by `C |v|` for every `v`. -/
lemma exists_lip_bound (f : UnitAddCircle → ℝ) (hf : IsSmoothCircle f) (x : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |residualFun f x v| ≤ C * |v| := by
  obtain ⟨M, hM⟩ := exists_bound_lift f hf
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hFc : ContDiff ℝ ∞ (fun u : ℝ => f (u : UnitAddCircle)) := hf
  have hdc : Continuous (deriv fun u : ℝ => f (u : UnitAddCircle)) :=
    hFc.continuous_deriv (by simp)
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := x - 1) (b := x + 1)).exists_bound_of_continuousOn
    hdc.continuousOn
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL x ⟨by linarith, by linarith⟩)
  refine ⟨L + 2 * M, by positivity, fun v => ?_⟩
  by_cases hv : |v| ≤ 1
  · have hv' := abs_le.1 hv
    have hmem : x - v ∈ Icc (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
    have hx : x ∈ Icc (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hFc.differentiable (by simp) z) (fun z hz => hL z hz) (convex_Icc _ _) hx hmem
    calc |residualFun f x v|
        = ‖(fun u : ℝ => f (u : UnitAddCircle)) (x - v) -
            (fun u : ℝ => f (u : UnitAddCircle)) x‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
          rfl
      _ ≤ L * ‖x - v - x‖ := hmvt
      _ = L * |v| := by rw [show x - v - x = -v by ring, norm_neg, Real.norm_eq_abs]
      _ ≤ (L + 2 * M) * |v| := by nlinarith [abs_nonneg v]
  · rw [not_le] at hv
    have h1 : |residualFun f x v| ≤ 2 * M := by
      unfold residualFun
      have := abs_sub (f (x : UnitAddCircle)) (f ((x - v : ℝ) : UnitAddCircle))
      linarith [hM x, hM (x - v)]
    have h2 : 2 * M ≤ 2 * M * |v| := by nlinarith
    nlinarith [mul_nonneg hL0 (abs_nonneg v)]

/-! ### The Gamma substitution `t ↦ 1/t` -/

/-- The integral `∫_0^∞ e^{-a/t} t^{-s-1} dt` equals `Γ(s) a^{-s}`, and the integrand is integrable.
-/
lemma integral_inv_exp_rpow {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-a / t) * t ^ (-s - 1)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-a / t) * t ^ (-s - 1) = Real.Gamma s * a ^ (-s) := by
  set h : ℝ → ℝ := fun t => Real.exp (-a / t) * t ^ (-s - 1) with hh
  have himg : (fun t : ℝ => t⁻¹) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact inv_pos.2 ht
    · intro hy
      exact ⟨y⁻¹, inv_pos.2 hy, inv_inv y⟩
  have hf' : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) (Ioi 0) t :=
    fun t ht => (hasDerivAt_inv (ne_of_gt ht)).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t⁻¹) (Ioi 0) := fun p _ q _ hpq => by
    simpa using hpq
  have hpt : ∀ x ∈ Ioi (0 : ℝ), |-(x ^ 2)⁻¹| • h x⁻¹ = Real.exp (-a * x) * x ^ (s - 1) := by
    intro x hx
    have hx0 : 0 < x := hx
    rw [smul_eq_mul, abs_neg, abs_of_pos (inv_pos.2 (pow_pos hx0 2))]
    simp only [hh]
    rw [div_inv_eq_mul, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le,
      show -(-s - 1) = s + 1 by ring]
    have e : x ^ (s + 1) = x ^ (s - 1) * x ^ 2 := by
      rw [show s + 1 = (s - 1) + 2 by ring, Real.rpow_add hx0, Real.rpow_two]
    rw [e]
    field_simp
  have hint : IntegrableOn (fun x : ℝ => |-(x ^ 2)⁻¹| • h x⁻¹) (Ioi 0) :=
    (integrableOn_exp_mul_rpow_sub_one hs ha).congr_fun (fun x hx => (hpt x hx).symm)
      measurableSet_Ioi
  have hA : IntegrableOn h (Ioi 0) := by
    have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hf' hinj h).2
      hint
    rwa [himg] at this
  refine ⟨hA, ?_⟩
  have hV := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf' hinj h
  rw [himg] at hV
  rw [hV, setIntegral_congr_fun measurableSet_Ioi (fun x hx => hpt x hx)]
  have hG := rpow_neg_eq_gamma_inv_mul_integral hs ha
  have hΓ : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  rw [hG, ← mul_assoc, mul_inv_cancel₀ hΓ, one_mul]

/-- The identity `(u²/4)^p = |u|^{2p} 2^{-2p}`. -/
lemma rpow_sq_quarter (u p : ℝ) : (u ^ 2 / 4) ^ p = |u| ^ (2 * p) * 2 ^ (-(2 * p)) := by
  rw [Real.div_rpow (sq_nonneg u) (by norm_num), ← abs_rpow_two_mul_eq]
  have h4 : (4 : ℝ) ^ p = 2 ^ (2 * p) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
      ← Real.rpow_mul (by norm_num)]
  rw [h4, Real.rpow_neg (by norm_num), div_eq_mul_inv]

/-- The time integral of the heat kernel against `t^{-1-γ}`: for `u ≠ 0`,
`∫_0^∞ G_t(u) t^{-1-γ} dt = (4π)^{-1/2} 2^{1+2γ} Γ(γ+1/2) |u|^{-1-2γ}`. -/
lemma gauss_time_integral {γ : ℝ} (hγ : 0 < γ) {u : ℝ} (hu : u ≠ 0) :
    IntegrableOn (fun t : ℝ => gaussKernel t u * t ^ (-1 - γ)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), gaussKernel t u * t ^ (-1 - γ) =
        singularWeight γ * |u| ^ (-(1 + 2 * γ)) := by
  have hu2 : 0 < u ^ 2 := by positivity
  have ha : 0 < u ^ 2 / 4 := by positivity
  have hs : 0 < γ + 1 / 2 := by linarith
  obtain ⟨hI, hV⟩ := integral_inv_exp_rpow ha hs
  have hpt : ∀ t ∈ Ioi (0 : ℝ), gaussKernel t u * t ^ (-1 - γ) =
      (4 * π) ^ (-(1 / 2 : ℝ)) * (Real.exp (-(u ^ 2 / 4) / t) * t ^ (-(γ + 1 / 2) - 1)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    unfold gaussKernel
    rw [Real.mul_rpow (by positivity) ht0.le, show -u ^ 2 / (4 * t) = -(u ^ 2 / 4) / t by ring,
      show -(γ + 1 / 2) - 1 = (-(1 / 2 : ℝ)) + (-1 - γ) by ring, Real.rpow_add ht0]
    ring
  have hIeq : IntegrableOn (fun t : ℝ => gaussKernel t u * t ^ (-1 - γ)) (Ioi 0) :=
    IntegrableOn.congr_fun (hI.const_mul ((4 * π) ^ (-(1 / 2 : ℝ))))
      (fun t ht => (hpt t ht).symm) measurableSet_Ioi
  refine ⟨hIeq, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpt t ht),
    MeasureTheory.integral_const_mul, hV, rpow_sq_quarter,
    show 2 * (-(γ + 1 / 2)) = -(1 + 2 * γ) by ring, neg_neg]
  unfold singularWeight
  ring

/-! ### Fubini: the time integral of the residual -/

/-- The time integral of the residual against `t^{-1-γ}`, rewritten by Fubini as an integral over
`ℝ`. The integrability of `v ↦ (f(x) - f(x - v)) |v|^{-1-2γ}` comes from the marginal of the
product integrable. -/
lemma fubini_residual {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) (f : UnitAddCircle → ℝ)
    (hf : IsSmoothCircle f) (x : ℝ) :
    Integrable (fun v : ℝ => residualFun f x v * |v| ^ (-(1 + 2 * γ))) ∧
      ∫ t in Ioi (0 : ℝ), (∫ v, residualFun f x v * gaussKernel t v) * t ^ (-1 - γ) =
        ∫ v, residualFun f x v * (singularWeight γ * |v| ^ (-(1 + 2 * γ))) := by
  obtain ⟨M, hM⟩ := exists_bound_lift f hf
  obtain ⟨C, hC0, hC⟩ := exists_lip_bound f hf x
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hfc : Continuous fun u : ℝ => f (u : UnitAddCircle) :=
    (show ContDiff ℝ ∞ (fun u : ℝ => f (u : UnitAddCircle)) from hf).continuous
  have hΦc : Continuous (residualFun f x) := by
    unfold residualFun
    exact continuous_const.sub (hfc.comp (continuous_const.sub continuous_id))
  have hΦM : ∀ v, |residualFun f x v| ≤ 2 * M := by
    intro v
    unfold residualFun
    have := abs_sub (f (x : UnitAddCircle)) (f ((x - v : ℝ) : UnitAddCircle))
    linarith [hM x, hM (x - v)]
  have hcpos : 0 < singularWeight γ := by
    unfold singularWeight
    have : 0 < Real.Gamma (γ + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  set F : ℝ → ℝ → ℝ := fun t v => residualFun f x v * (gaussKernel t v * t ^ (-1 - γ)) with hF
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun p : ℝ × ℝ => residualFun f x p.2) :=
      hΦc.measurable.comp measurable_snd
    have h2 : Measurable (fun p : ℝ × ℝ => gaussKernel p.1 p.2) := by
      unfold gaussKernel
      fun_prop
    have h3 : Measurable (fun p : ℝ × ℝ => p.1 ^ (-1 - γ)) := measurable_fst.pow_const _
    exact h1.mul (h2.mul h3)
  have hv0 : ∀ᵐ v : ℝ ∂volume, v ≠ 0 := by
    rw [ae_iff]
    simp
  -- for a.e. t > 0, the v-integral of F t is integrable
  have hin : ∀ᵐ t ∂μ, Integrable (fun v => F t v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    refine Integrable.mono'
      (((gaussKernel_integrable ht0).mul_const (t ^ (-1 - γ))).const_mul (2 * M))
      (hΦc.mul ((gaussKernel_continuous ht0).mul continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    have hT : 0 ≤ t ^ (-1 - γ) := Real.rpow_nonneg ht0.le _
    simp only [hF]
    rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (gaussKernel_nonneg ht0 v) hT),
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hΦM v) (mul_nonneg (gaussKernel_nonneg ht0 v) hT)
  -- the norm integral in v at a positive time
  have hnorm_t : ∀ t : ℝ, 0 < t → ∫ v, ‖F t v‖ =
      t ^ (-1 - γ) * ∫ v, |residualFun f x v| * gaussKernel t v := by
    intro t ht0
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [hF]
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (gaussKernel_nonneg ht0 v),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
    ring
  have hA_M : ∀ t : ℝ, 0 < t → ∫ v, |residualFun f x v| * gaussKernel t v ≤ 2 * M := by
    intro t ht0
    have hint1 : Integrable (fun v => |residualFun f x v| * gaussKernel t v) := by
      refine Integrable.mono' ((gaussKernel_integrable ht0).const_mul (2 * M))
        (hΦc.abs.mul (gaussKernel_continuous ht0)).aestronglyMeasurable
        (ae_of_all _ fun v => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (gaussKernel_nonneg ht0 v))]
      exact mul_le_mul_of_nonneg_right (hΦM v) (gaussKernel_nonneg ht0 v)
    calc ∫ v, |residualFun f x v| * gaussKernel t v
        ≤ ∫ v, 2 * M * gaussKernel t v :=
          integral_mono hint1 ((gaussKernel_integrable ht0).const_mul _)
            (fun v => mul_le_mul_of_nonneg_right (hΦM v) (gaussKernel_nonneg ht0 v))
      _ = 2 * M := by rw [MeasureTheory.integral_const_mul, integral_gaussKernel ht0, mul_one]
  have hA_sqrt : ∀ t : ℝ, 0 < t → ∫ v, |residualFun f x v| * gaussKernel t v ≤ 2 * C * √t := by
    intro t ht0
    have hint1 : Integrable (fun v => |residualFun f x v| * gaussKernel t v) := by
      refine Integrable.mono' ((gaussKernel_integrable ht0).const_mul (2 * M))
        (hΦc.abs.mul (gaussKernel_continuous ht0)).aestronglyMeasurable
        (ae_of_all _ fun v => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (gaussKernel_nonneg ht0 v))]
      exact mul_le_mul_of_nonneg_right (hΦM v) (gaussKernel_nonneg ht0 v)
    calc ∫ v, |residualFun f x v| * gaussKernel t v
        ≤ ∫ v, C * (|v| * gaussKernel t v) :=
          integral_mono hint1 ((integrable_abs_mul_gaussKernel ht0).const_mul C)
            (fun v => by
              have := mul_le_mul_of_nonneg_right (hC v) (gaussKernel_nonneg ht0 v)
              linarith [this, show C * |v| * gaussKernel t v = C * (|v| * gaussKernel t v) by ring])
      _ = C * ∫ v, |v| * gaussKernel t v := MeasureTheory.integral_const_mul _ _
      _ ≤ C * (2 * √t) := mul_le_mul_of_nonneg_left (integral_abs_mul_gaussKernel_le ht0) hC0
      _ = 2 * C * √t := by ring
  -- the outer integrability in t
  have hmeas_out : AEStronglyMeasurable (fun t => ∫ v, ‖F t v‖) volume := by
    have hm : StronglyMeasurable (Function.uncurry fun t v => ‖F t v‖) :=
      hFm.norm.stronglyMeasurable
    exact (hm.integral_prod_right' (ν := volume)).aestronglyMeasurable
  have hout : Integrable (fun t => ∫ v, ‖F t v‖) μ := by
    have hIO : IntegrableOn (fun t => ∫ v, ‖F t v‖) (Ioi 0) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
      refine IntegrableOn.union ?_ ?_
      · have hb : IntegrableOn (fun t : ℝ => 2 * C * t ^ (-1 / 2 - γ)) (Ioc 0 1) :=
          ((intervalIntegral.intervalIntegrable_rpow'
            (by linarith : (-1 : ℝ) < -1 / 2 - γ)).const_mul (2 * C)).1
        refine Integrable.mono' hb hmeas_out.restrict
          (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_))
        have ht0 : 0 < t := ht.1
        rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _), hnorm_t t ht0]
        calc t ^ (-1 - γ) * ∫ v, |residualFun f x v| * gaussKernel t v
            ≤ t ^ (-1 - γ) * (2 * C * √t) :=
              mul_le_mul_of_nonneg_left (hA_sqrt t ht0) (Real.rpow_nonneg ht0.le _)
          _ = 2 * C * t ^ (-1 / 2 - γ) := by
              rw [Real.sqrt_eq_rpow, show (-1 / 2 - γ : ℝ) = (-1 - γ) + 1 / 2 by ring,
                Real.rpow_add ht0]
              ring
      · have hb : IntegrableOn (fun t : ℝ => 2 * M * t ^ (-1 - γ)) (Ioi 1) :=
          (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - γ < -1) zero_lt_one).const_mul (2 * M)
        refine Integrable.mono' hb hmeas_out.restrict
          (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _), hnorm_t t ht0]
        calc t ^ (-1 - γ) * ∫ v, |residualFun f x v| * gaussKernel t v
            ≤ t ^ (-1 - γ) * (2 * M) :=
              mul_le_mul_of_nonneg_left (hA_M t ht0) (Real.rpow_nonneg ht0.le _)
          _ = 2 * M * t ^ (-1 - γ) := by ring
    exact hIO
  have hprod : Integrable (Function.uncurry F) (μ.prod volume) :=
    (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨hin, hout⟩
  have hswap := integral_integral_swap (f := F) hprod
  -- value of the inner integral in t at a point `v ≠ 0`
  have hinner : ∀ v : ℝ, v ≠ 0 → ∫ t, F t v ∂μ = residualFun f x v * (singularWeight γ * |v| ^ (-(1 + 2 * γ))) := by
    intro v hv
    simp only [hF]
    rw [MeasureTheory.integral_const_mul, (gauss_time_integral hγ0 hv).2]
  have hnv : ∀ v : ℝ, v ≠ 0 → ∫ t, ‖Function.uncurry F (t, v)‖ ∂μ =
      |residualFun f x v| * (singularWeight γ * |v| ^ (-(1 + 2 * γ))) := by
    intro v hv
    have h1 : ∫ t, ‖Function.uncurry F (t, v)‖ ∂μ =
        ∫ t, |residualFun f x v| * (gaussKernel t v * t ^ (-1 - γ)) ∂μ := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : 0 < t := ht
      have hT : 0 ≤ t ^ (-1 - γ) := Real.rpow_nonneg ht0.le _
      simp only [hF, Function.uncurry_apply_pair]
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (gaussKernel_nonneg ht0 v) hT)]
    rw [h1, MeasureTheory.integral_const_mul, (gauss_time_integral hγ0 hv).2]
  refine ⟨?_, ?_⟩
  · -- integrability of the residual weighted by `|v|^{-1-2γ}`, from the marginal
    have hmarg := hprod.integral_norm_prod_right
    have hmeasψ : Measurable (fun v : ℝ => residualFun f x v * |v| ^ (-(1 + 2 * γ))) :=
      hΦc.measurable.mul (continuous_abs.measurable.pow_const _)
    refine Integrable.mono' (hmarg.const_mul (1 / singularWeight γ)) hmeasψ.aestronglyMeasurable ?_
    filter_upwards [hv0] with v hv
    rw [hnv v hv, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg v) _)]
    exact le_of_eq (by field_simp)
  · have hLHS : ∫ t in Ioi (0 : ℝ), (∫ v, residualFun f x v * gaussKernel t v) * t ^ (-1 - γ) =
        ∫ t, ∫ v, F t v ∂volume ∂μ := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      simp only [hF]
      rw [← MeasureTheory.integral_mul_const]
      congr 1
      funext v
      ring
    rw [hLHS, hswap]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hv0] with v hv
    exact hinner v hv

/-- The integral over the subtype `Ioi 0` (for real-valued integrands) equals the set integral. -/
lemma integral_subtype_Ioi_eq_real (G : (t : ℝ) → 0 < t → ℝ) (Φ : ℝ → ℝ)
    (h : ∀ (t : ℝ) (ht : 0 < t), G t ht = Φ t) :
    ∫ t, G t.1 t.2 ∂(Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume) =
      ∫ t in Ioi (0 : ℝ), Φ t := by
  rw [← MeasureTheory.integral_subtype_comap measurableSet_Ioi Φ]
  congr 1
  funext t
  exact h t.1 t.2

/-! ### The coefficient `C_γ` -/

/-- The constant `C_γ` is `γ/Γ(1-γ)` times the weight of the time integral. -/
lemma singularConst_eq {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    singularConst γ = γ / Real.Gamma (1 - γ) * singularWeight γ := by
  have hΓ1 : 0 < Real.Gamma (1 - γ) := Real.Gamma_pos_of_pos (by linarith)
  have hrec : Real.Gamma (1 - γ) = -γ * Real.Gamma (-γ) := by
    have h := Real.Gamma_add_one (s := -γ) (neg_ne_zero.2 hγ0.ne')
    rw [show -γ + 1 = 1 - γ by ring] at h
    exact h
  have hGneg : Real.Gamma (-γ) = -(Real.Gamma (1 - γ) / γ) := by
    rw [hrec]
    field_simp
  have habs : |Real.Gamma (-γ)| = Real.Gamma (1 - γ) / γ := by
    rw [hGneg, abs_neg, abs_of_pos (div_pos hΓ1 hγ0)]
  have h4 : (4 * π) ^ (-(1 / 2 : ℝ)) = (2 * √π)⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num),
      show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have h2 : (2 : ℝ) ^ (1 + 2 * γ) = 2 * 2 ^ (2 * γ) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hsπ : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hΓ0 : Real.Gamma (1 - γ) ≠ 0 := hΓ1.ne'
  unfold singularConst singularWeight
  rw [habs, h4, h2]
  field_simp

/-! ### The singular integral formula -/

/-- The singular integral formula for the fractional Laplacian on the unit circle, for
`0 < γ < 1/2`: the double sum `∑_n ∫_0^1` converges absolutely and
`(-Δ)^γ f(x) = C_γ ∑_n ∫_0^1 (f(x) - f(y)) / |x - y - n|^{1+2γ} dy`. -/
theorem fracLapSeries_singular {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) (f : UnitAddCircle → ℝ)
    (hf : IsSmoothCircle f) (x : ℝ) :
    Summable (fun n : ℤ => ∫ y in (0 : ℝ)..1,
      |(f (x : UnitAddCircle) - f (y : UnitAddCircle)) / |x - y - (n : ℝ)| ^ (1 + 2 * γ)|) ∧
    fracLapSeries γ f hf x = ((singularConst γ * ∑' n : ℤ, ∫ y in (0 : ℝ)..1,
      (f (x : UnitAddCircle) - f (y : UnitAddCircle)) / |x - y - (n : ℝ)| ^ (1 + 2 * γ) : ℝ) :
        ℂ) := by
  obtain ⟨hψint, hfub⟩ := fubini_residual hγ0 hγ1 f hf x
  set ψ : ℝ → ℝ := fun v => residualFun f x v * |v| ^ (-(1 + 2 * γ)) with hψdef
  set χ : ℝ → ℝ := fun w => (f (x : UnitAddCircle) - f (w : UnitAddCircle)) /
    |x - w| ^ (1 + 2 * γ) with hχdef
  have hψχ : ∀ v, ψ v = χ (x - v) := by
    intro v
    simp only [hψdef, hχdef, residualFun]
    rw [show x - (x - v) = v by ring, Real.rpow_neg (abs_nonneg v), div_eq_mul_inv]
  have hfun : (fun w : ℝ => ψ (x - w)) = χ := by
    funext w
    show ψ (x - w) = χ w
    rw [hψχ (x - w), show x - (x - w) = w by ring]
  have hχint : Integrable χ := by
    rw [← hfun]
    exact hψint.comp_sub_left x
  have hχval : ∫ w, χ w = ∫ v, ψ v := by
    rw [← MeasureTheory.integral_sub_left_eq_self ψ volume x]
    refine MeasureTheory.integral_congr_ae (ae_of_all _ fun w => ?_)
    show χ w = ψ (x - w)
    rw [hψχ (x - w), show x - (x - w) = w by ring]
  have hpt : ∀ (n : ℤ) (y : ℝ), χ (y + n) = (f (x : UnitAddCircle) - f (y : UnitAddCircle)) /
      |x - y - (n : ℝ)| ^ (1 + 2 * γ) := by
    intro n y
    simp only [hχdef]
    rw [show x - (y + n) = x - y - n by ring, lift_add_int f y n]
  have hsumχ := hasSum_unfold_plus χ hχint
  have hval_sum : (∑' n : ℤ, ∫ y in (0 : ℝ)..1,
      (f (x : UnitAddCircle) - f (y : UnitAddCircle)) / |x - y - (n : ℝ)| ^ (1 + 2 * γ)) =
        ∫ w, χ w := by
    rw [← hsumχ.tsum_eq]
    exact tsum_congr fun n => by
      congr 1
      funext y
      rw [hpt n y]
  have hmain : ∫ v, residualFun f x v * (singularWeight γ * |v| ^ (-(1 + 2 * γ))) =
      singularWeight γ * ∫ w, χ w := by
    rw [hχval, ← MeasureTheory.integral_const_mul]
    congr 1
    funext v
    simp only [hψdef]
    ring
  have hsub := integral_subtype_Ioi_eq_real
    (fun (t : ℝ) (ht : 0 < t) => (f (x : UnitAddCircle) - heatConvolution f ht x) * t ^ (-1 - γ))
    (fun t => (∫ v, residualFun f x v * gaussKernel t v) * t ^ (-1 - γ))
    (fun t ht => by rw [heat_residual f hf ht x])
  refine ⟨?_, ?_⟩
  · refine Summable.congr (hasSum_unfold_plus (fun w => |χ w|) hχint.abs).summable (fun n => ?_)
    congr 1
    funext y
    simp only [hpt]
  · rw [fracLapSeries_eq_heat hγ0 (by linarith) f hf x, hsub, hfub, hmain,
      singularConst_eq hγ0 (by linarith), ← hval_sum]
    congr 1
    ring

end Riesz1

end
