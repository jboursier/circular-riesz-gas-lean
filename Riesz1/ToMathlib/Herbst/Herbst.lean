/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Herbst.Mgf
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The Herbst argument

A logarithmic Sobolev inequality for a probability measure `μ` gives a Gaussian bound on the
exponential moments of a function `F` with bounded gradient. Let `Λ(t)` be the logarithm of
`∫ exp (t F) dμ`. Applying the inequality to `q = exp (t F / 2)` gives
`t Λ'(t) - Λ(t) ≤ (w/2) t² L²`, where `L` bounds the gradient of `F`. Integrating
`(Λ(t) / t)' ≤ w L² / 2` from `0` to `t` gives the bound for positive `t`, and applying it to
`-F` gives the bound for negative `t`.

The main result is `Riesz1.herbst_log_mgf_le`. Its hypothesis `hLSI` is the logarithmic Sobolev
inequality itself, required for every smooth bounded `q` with bounded gradient.
-/

public section

open MeasureTheory Filter Topology Set
namespace Riesz1

/-- The logarithmic Sobolev inequality applied to `q = exp (s F / 2)` gives the tilted bound
`s M'(s) - M(s) log M(s) ≤ (w/2) s² L² M(s)`, where `M(s) = ∫ exp (s F) dμ`. -/
lemma herbst_tilted_ineq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {w : ℝ}
    (hw : 0 < w)
    (hLSI : ∀ q : E → ℝ, ContDiff ℝ 1 q → (∃ C, ∀ x, |q x| ≤ C) →
      (∃ C, ∀ x, ‖fderiv ℝ q x‖ ≤ C) →
      ∫ x, q x ^ 2 * Real.log (q x ^ 2) ∂μ - (∫ x, q x ^ 2 ∂μ) * Real.log (∫ x, q x ^ 2 ∂μ)
        ≤ 2 * w * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, |F x| ≤ C)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (s : ℝ) :
    s * ∫ x, F x * Real.exp (s * F x) ∂μ
        - (∫ x, Real.exp (s * F x) ∂μ) * Real.log (∫ x, Real.exp (s * F x) ∂μ)
      ≤ w / 2 * s ^ 2 * L ^ 2 * ∫ x, Real.exp (s * F x) ∂μ := by
  have hdiff : ∀ x, DifferentiableAt ℝ F x := fun x => (hF.differentiable one_ne_zero) x
  have hg : ContDiff ℝ 1 (fun x => s / 2 * F x) := contDiff_const.mul hF
  have hq1 : ContDiff ℝ 1 (fun x => Real.exp (s / 2 * F x)) := Real.contDiff_exp.comp hg
  have hqb : ∃ D, ∀ x, |Real.exp (s / 2 * F x)| ≤ D :=
    ⟨Real.exp (|s / 2| * C), fun x => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact herbst_exp_le hC (s / 2) x⟩
  have hqd : ∃ D, ∀ x, ‖fderiv ℝ (fun y => Real.exp (s / 2 * F y)) x‖ ≤ D :=
    ⟨Real.exp (|s / 2| * C) * (|s / 2| * L), fun x => by
      rw [herbst_norm_fderiv_exp (hdiff x) (s / 2)]
      exact mul_le_mul (herbst_exp_le hC (s / 2) x)
        (mul_le_mul_of_nonneg_left (hL x) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le⟩
  -- Under `q = exp (s F / 2)` the squares are `exp (s F)` and the logarithms are `s F`.
  have e1 : ∀ x, Real.exp (s / 2 * F x) ^ 2 = Real.exp (s * F x) := fun x => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hL' := hLSI _ hq1 hqb hqd
  simp only [e1, Real.log_exp] at hL'
  -- The entropy term equals `s ∫ F exp (s F)`.
  have hint : ∫ x, Real.exp (s * F x) * (s * F x) ∂μ
      = s * ∫ x, F x * Real.exp (s * F x) ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hint] at hL'
  -- The gradient term is at most `(s/2)² L²` times `M(s)`.
  have hgrad : ∫ x, ‖fderiv ℝ (fun y => Real.exp (s / 2 * F y)) x‖ ^ 2 ∂μ
      ≤ (s / 2) ^ 2 * L ^ 2 * ∫ x, Real.exp (s * F x) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
      ((herbst_integrable_exp hF.continuous hC s).const_mul _)
      (Eventually.of_forall fun x => ?_)
    show ‖fderiv ℝ (fun y => Real.exp (s / 2 * F y)) x‖ ^ 2
      ≤ (s / 2) ^ 2 * L ^ 2 * Real.exp (s * F x)
    rw [herbst_norm_fderiv_exp (hdiff x) (s / 2)]
    calc (Real.exp (s / 2 * F x) * (|s / 2| * ‖fderiv ℝ F x‖)) ^ 2
        = Real.exp (s / 2 * F x) ^ 2 * ((s / 2) ^ 2 * ‖fderiv ℝ F x‖ ^ 2) := by
          rw [mul_pow, mul_pow, sq_abs]
      _ ≤ Real.exp (s / 2 * F x) ^ 2 * ((s / 2) ^ 2 * L ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hL x) 2)
              (sq_nonneg _)) (sq_nonneg _)
      _ = (s / 2) ^ 2 * L ^ 2 * Real.exp (s * F x) := by
          rw [e1 x]
          ring
  have h2w : 0 ≤ 2 * w := by linarith
  have h3 := mul_le_mul_of_nonneg_left hgrad h2w
  linarith

/-- The Herbst bound for a positive parameter `t`. -/
lemma herbst_log_mgf_le_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {w : ℝ}
    (hw : 0 < w)
    (hLSI : ∀ q : E → ℝ, ContDiff ℝ 1 q → (∃ C, ∀ x, |q x| ≤ C) →
      (∃ C, ∀ x, ‖fderiv ℝ q x‖ ≤ C) →
      ∫ x, q x ^ 2 * Real.log (q x ^ 2) ∂μ - (∫ x, q x ^ 2 ∂μ) * Real.log (∫ x, q x ^ 2 ∂μ)
        ≤ 2 * w * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ)
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ x, |F x| ≤ C)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) {t : ℝ} (ht : 0 < t) :
    Real.log (∫ x, Real.exp (t * F x) ∂μ) ≤ t * ∫ x, F x ∂μ + w / 2 * t ^ 2 * L ^ 2 := by
  -- Names for the moment generating function, its derivative and the mean of `F`.
  obtain ⟨M, hM⟩ : ∃ M : ℝ → ℝ, M = fun r => ∫ x, Real.exp (r * F x) ∂μ := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ → ℝ, M' = fun r => ∫ x, F x * Real.exp (r * F x) ∂μ :=
    ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∫ x, F x ∂μ := ⟨_, rfl⟩
  have hMr : ∀ r, M r = ∫ x, Real.exp (r * F x) ∂μ := fun r => by rw [hM]
  have hM'r : ∀ r, M' r = ∫ x, F x * Real.exp (r * F x) ∂μ := fun r => by rw [hM']
  have hMd : ∀ r, HasDerivAt M (M' r) r := fun r => by
    rw [hM, hM']
    exact herbst_hasDerivAt_mgf hF.continuous hC r
  have hMpos : ∀ r, 0 < M r := fun r => by
    rw [hMr]
    exact herbst_integral_exp_pos hF.continuous hC r
  have hM0 : M 0 = 1 := by
    rw [hMr]
    simp
  have hM'0 : M' 0 = A := by
    rw [hM'r, hA]
    simp
  -- The differential inequality `r M'(r) / M(r) - log M(r) ≤ (w/2) r² L²` for every `r`.
  have hkey : ∀ r, r * (M' r / M r) - Real.log (M r) ≤ w / 2 * r ^ 2 * L ^ 2 := by
    intro r
    have h := herbst_tilted_ineq hw hLSI hF hC hL r
    rw [← hMr r, ← hM'r r] at h
    have hne : M r ≠ 0 := (hMpos r).ne'
    have e : r * (M' r / M r) - Real.log (M r)
        = (r * M' r - M r * Real.log (M r)) / M r := by
      rw [sub_div, mul_div_assoc, mul_div_cancel_left₀ _ hne]
    rw [e, div_le_iff₀ (hMpos r)]
    linarith
  -- The function `ψ(r) = log M(r) - r A - (w/2) L² r²` vanishes at zero with zero derivative.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ,
      ψ = fun r => Real.log (M r) - r * A - w / 2 * L ^ 2 * r ^ 2 := ⟨_, rfl⟩
  have hψd : ∀ r, HasDerivAt ψ (M' r / M r - A - w * L ^ 2 * r) r := by
    intro r
    have h1 : HasDerivAt (fun y => Real.log (M y)) (M' r / M r) r :=
      (hMd r).log (hMpos r).ne'
    have h2 : HasDerivAt (fun y => y * A) A r := hasDerivAt_mul_const (x := r) A
    have h := (h1.sub h2).sub ((hasDerivAt_pow 2 r).const_mul (w / 2 * L ^ 2))
    rw [hψ]
    convert h using 1
    norm_num
    ring
  have hψ0 : HasDerivAt ψ 0 0 := by
    convert hψd 0 using 1
    rw [hM0, hM'0]
    ring
  have hψ_zero : ψ 0 = 0 := by
    rw [hψ]
    simp [hM0]
  -- The quotient `ψ(r) / r` has nonpositive derivative on `(0, ∞)`.
  have hg : ∀ r : ℝ, 0 < r → HasDerivAt (fun y => ψ y / y)
      (((M' r / M r - A - w * L ^ 2 * r) * r - ψ r * 1) / r ^ 2) r := fun r hr =>
    (hψd r).div (hasDerivAt_id' r) hr.ne'
  have hgnp : ∀ r : ℝ, 0 < r → ((M' r / M r - A - w * L ^ 2 * r) * r - ψ r * 1) / r ^ 2 ≤ 0 := by
    intro r _
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg r)
    have hk := hkey r
    simp only [hψ]
    linarith
  have hanti : AntitoneOn (fun y => ψ y / y) (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · intro r hr
      exact (hg r (Set.mem_Ioi.mp hr)).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      intro r hr
      exact (hg r (Set.mem_Ioi.mp hr)).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro r hr
      rw [(hg r (Set.mem_Ioi.mp hr)).deriv]
      exact hgnp r (Set.mem_Ioi.mp hr)
  -- The quotient `ψ(r) / r` tends to `0` as `r` decreases to `0`, since `ψ'(0) = 0`.
  have hlim : Tendsto (fun y => ψ y / y) (𝓝[>] 0) (𝓝 0) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hψ0).mono_left
      (nhdsWithin_mono _ fun r (hr : r ∈ Ioi 0) => (Set.mem_Ioi.mp hr).ne')
    refine Tendsto.congr (fun r => ?_) h
    simp [slope_def_field, hψ_zero]
  -- Monotonicity bounds `ψ(t) / t` by its limit at zero.
  have hgt : ψ t / t ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with r hr
    exact hanti (Set.mem_Ioi.mpr hr.1) (Set.mem_Ioi.mpr ht) hr.2.le
  have hψt : ψ t ≤ 0 := by
    have h := (div_le_iff₀ ht).mp hgt
    linarith
  simp only [hψ] at hψt
  rw [← hMr t, ← hA]
  linarith

/-- **Herbst bound.** Let `μ` be a probability measure on the Euclidean space `ℝ^d`, and let
`w > 0`. Suppose that the logarithmic Sobolev inequality with coefficient `2w` holds for every
smooth bounded `q` with bounded gradient. Let `F` be a bounded `C¹` function with gradient
bounded by `L`. Then for every real `t`,
`log ∫ exp (t F) dμ ≤ t ∫ F dμ + (w/2) t² L²`. -/
theorem herbst_log_mgf_le {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (w : ℝ) (hw : 0 < w)
    (hLSI : ∀ q : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 q →
      (∃ C, ∀ x, |q x| ≤ C) → (∃ C, ∀ x, ‖fderiv ℝ q x‖ ≤ C) →
      ∫ x, q x ^ 2 * Real.log (q x ^ 2) ∂μ -
          (∫ x, q x ^ 2 ∂μ) * Real.log (∫ x, q x ^ 2 ∂μ)
        ≤ 2 * w * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ)
    (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiff ℝ 1 F) (hFb : ∃ C, ∀ x, |F x| ≤ C)
    (L : ℝ) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (t : ℝ) :
    Real.log (∫ x, Real.exp (t * F x) ∂μ) ≤ t * ∫ x, F x ∂μ + w / 2 * t ^ 2 * L ^ 2 := by
  obtain ⟨C, hC⟩ := hFb
  rcases lt_trichotomy t 0 with ht | ht | ht
  · -- For negative `t`, apply the positive case to `-F` and the parameter `-t`.
    have hC' : ∀ x, |(-F) x| ≤ C := fun x => by
      rw [Pi.neg_apply, abs_neg]
      exact hC x
    have hL' : ∀ x, ‖fderiv ℝ (-F) x‖ ≤ L := fun x => by
      rw [fderiv_neg, norm_neg]
      exact hL x
    have h := herbst_log_mgf_le_pos hw hLSI hF.neg hC' hL' (t := -t) (by linarith)
    simp only [neg_mul_neg, integral_neg] at h
    linarith
  · subst ht
    simp
  · exact herbst_log_mgf_le_pos hw hLSI hF hC hL ht

end Riesz1
