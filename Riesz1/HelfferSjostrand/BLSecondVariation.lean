/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Second variation of exponential comparisons

The analytic step is separated from the geometric midpoint comparison.
Its hypotheses on exponential integrability are discharged from compactness
when it is applied to smooth observables on bounded domains.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace Riesz1

/-- The second derivative at a zero local minimum is nonnegative. -/
theorem bl_second_variation_nonneg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hzero : f 0 = 0) (hfirst : deriv f 0 = 0)
    (hn : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ f t) : 0 ≤ deriv (deriv f) 0 := by
  have ht := Real.taylor_tendsto convex_univ (mem_univ (0 : ℝ)) hf.contDiffOn
  simp only [nhdsWithin_univ] at ht
  have hpoly (t : ℝ) : taylorWithinEval f 2 univ 0 t =
      (deriv (deriv f) 0 / 2) * t ^ 2 := by
    simp [show (2 : ℕ) = 1 + 1 from rfl, taylorWithinEval_succ,
      iteratedDerivWithin_univ, iteratedDeriv_succ, hzero, hfirst, smul_eq_mul]
    ring
  have ht' : Tendsto (fun t : ℝ => f t / t ^ 2 - deriv (deriv f) 0 / 2)
      (𝓝[≠] 0) (𝓝 0) := by
    have htne := ht.mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    apply htne.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht0
    have ht0' : t ≠ 0 := ht0
    simp only [hpoly, sub_zero]
    field_simp
  have hlim : Tendsto (fun t : ℝ => f t / t ^ 2) (𝓝[≠] 0)
      (𝓝 (deriv (deriv f) 0 / 2)) := by
    have hh := ht'.add_const (deriv (deriv f) 0 / 2)
    simpa using hh
  have hpos : 0 ≤ deriv (deriv f) 0 / 2 := by
    apply ge_of_tendsto hlim
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with t ht
    exact div_nonneg ht (sq_nonneg t)
  linarith

/-- Second variation of the squared exponential comparison. This internal
analytic helper assumes exponential integrability. Geometric applications
derive that condition rather than adding it as a hypothesis of their statements. -/
theorem bl_second_variation_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ}
    (hX : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ)
    (hY : ∀ t : ℝ, Integrable (fun x => Real.exp (t * Y x)) μ)
    (hcmp : ∀ᶠ t : ℝ in 𝓝 0, mgf X μ t * mgf X μ (-t) ≤ (mgf Y μ (t ^ 2)) ^ 2) :
    (∫ x, X x ^ 2 ∂μ) - (∫ x, X x ∂μ) ^ 2 ≤ 2 * ∫ x, Y x ∂μ := by
  have hIX : integrableExpSet X μ = univ := Set.eq_univ_of_forall hX
  have hIY : integrableExpSet Y μ = univ := Set.eq_univ_of_forall hY
  have hix (t : ℝ) : t ∈ interior (integrableExpSet X μ) := by simp [hIX]
  have hiy (t : ℝ) : t ∈ interior (integrableExpSet Y μ) := by simp [hIY]
  let MX := mgf X μ
  let MY := mgf Y μ
  let DX : ℝ → ℝ := fun t => ∫ x, X x * Real.exp (t * X x) ∂μ
  let DY : ℝ → ℝ := fun t => ∫ x, Y x * Real.exp (t * Y x) ∂μ
  have hdX (t : ℝ) : HasDerivAt MX (DX t) t := hasDerivAt_mgf (hix t)
  have hdY (t : ℝ) : HasDerivAt MY (DY t) t := hasDerivAt_mgf (hiy t)
  have hddX : HasDerivAt DX (∫ x, X x ^ 2 ∂μ) 0 := by
    simpa [DX] using hasDerivAt_integral_pow_mul_exp_real (hix 0) 1
  have hddY : HasDerivAt DY (∫ x, Y x ^ 2 ∂μ) 0 := by
    simpa [DY] using hasDerivAt_integral_pow_mul_exp_real (hiy 0) 1
  have hcX : ContDiff ℝ 2 MX := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact (analyticAt_mgf (hix t)).contDiffAt
  have hcY : ContDiff ℝ 2 MY := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact (analyticAt_mgf (hiy t)).contDiffAt
  let f : ℝ → ℝ := fun t => (MY (t ^ 2)) ^ 2 - MX t * MX (-t)
  let df : ℝ → ℝ := fun t =>
    2 * MY (t ^ 2) * (DY (t ^ 2) * (2 * t)) -
      (DX t * MX (-t) + MX t * (DX (-t) * (-1)))
  have hdf (t : ℝ) : HasDerivAt f (df t) t := by
    have hsq := (hasDerivAt_id t).pow 2
    have hneg := (hasDerivAt_id t).neg
    convert ((hdY (t ^ 2)).comp t hsq |>.pow 2).sub
      ((hdX t).mul ((hdX (-t)).comp t hneg)) using 1
    · rfl
    · simp [df]
  have hdf0 : HasDerivAt df
      (4 * (∫ x, Y x ∂μ) - 2 * (∫ x, X x ^ 2 ∂μ) + 2 * (∫ x, X x ∂μ) ^ 2) 0 := by
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
      convert! (hasDerivAt_id (0 : ℝ)).pow 2 using 1; norm_num
    have hneg : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
    have hmy : HasDerivAt (fun t : ℝ => MY (t ^ 2)) (DY 0 * 0) 0 := by
      exact (hdY 0).comp_of_eq 0 hsq (by norm_num)
    have hdy : HasDerivAt (fun t : ℝ => DY (t ^ 2)) ((∫ x, Y x ^ 2 ∂μ) * 0) 0 := by
      exact hddY.comp_of_eq 0 hsq (by norm_num)
    have hmx : HasDerivAt (fun t : ℝ => MX (-t)) (DX 0 * (-1)) 0 := by
      exact (hdX 0).comp_of_eq 0 hneg (by norm_num)
    have hdx : HasDerivAt (fun t : ℝ => DX (-t)) ((∫ x, X x ^ 2 ∂μ) * (-1)) 0 := by
      exact hddX.comp_of_eq 0 hneg (by norm_num)
    have hlin := (hasDerivAt_id (0 : ℝ)).const_mul 2
    convert ((hmy.const_mul 2).mul (hdy.mul hlin)).sub
      ((hddX.mul hmx).add ((hdX 0).mul (hdx.mul_const (-1)))) using 1
    · rfl
    · simp [MY, MX, DY, DX]
      ring
  have hcf : ContDiff ℝ 2 f :=
    ((hcY.comp (contDiff_id.pow 2)).pow 2).sub
      (hcX.mul (hcX.comp contDiff_id.neg))
  have hf0 : f 0 = 0 := by simp [f, MX, MY]
  have hf1 : deriv f 0 = 0 := by rw [(hdf 0).deriv]; simp only [df, zero_pow,
    OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, mul_zero, neg_zero]; ring
  have hfn : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ f t := hcmp.mono (fun t ht => sub_nonneg.mpr ht)
  have hn := bl_second_variation_nonneg hcf hf0 hf1 hfn
  have hdeq : deriv f = df := funext (fun t => (hdf t).deriv)
  rw [hdeq, hdf0.deriv] at hn
  linarith

end Riesz1

end
