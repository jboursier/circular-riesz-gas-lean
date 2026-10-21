/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevConditioning
public import Riesz1.ToMathlib.WeightedSobolev.BoundedGradientCutoff
public import Riesz1.ToMathlib.WeightedSobolev.BoundedGradientFatou
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Logarithmic Sobolev inequality on the weighted `H¹` space

Let `ν = f γ_Ω^w` be the probability of the conditioning theorems, and let `U` be a set
with `ν`-almost every point in `closure U`. This file proves the logarithmic Sobolev inequality
`Ent_ν(F²) ≤ 2w ∫ |G|² dν` for every pair `(F, G)` of `IsWeightedH1 ν U`, with `G` the weak
gradient of `F`. This is Lemma 3.8 at its full generality (the closure of
the smooth test functions of `logSobolev_conditioning_smooth` in the weighted `H¹` norm).

The proof has four steps. First, `exists_hasCompactSupport_close` approximates `(F, G)` by smooth
compactly supported functions `ζ n` with weighted `H¹` error tending to zero. Second, the
inequality `logSobolev_conditioning_smooth` holds for each `ζ n`. Third, `ζ n → F` in measure gives
an almost everywhere convergent subsequence, and the squared `L²` norms converge. Fourth, Fatou's
lemma for the entropy (`integrable_mul_log_and_le_of_tendsto_ae`) passes the entropy inequality to
the limit. The only external hypothesis is `hBE : External.BakryEmery`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal ENNReal

namespace Riesz1.LogSobolevEntropy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth function with compact support is bounded, and so is its gradient. -/
theorem bounded_of_contDiff_hasCompactSupport {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hcs : HasCompactSupport ζ) :
    (∃ C, ∀ x, |ζ x| ≤ C) ∧ (∃ D, ∀ x, ‖gradient ζ x‖ ≤ D) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC⟩ := (hζ.continuous.abs).bounded_above_of_compact_support hcs.abs
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs, abs_abs] using hC x⟩
  · have hgcs : HasCompactSupport (fun x => ‖gradient ζ x‖) := by
      have hfd : (fun x => ‖gradient ζ x‖) = fun x => ‖fderiv ℝ ζ x‖ :=
        funext fun x => by simp [gradient]
      rw [hfd]
      exact (hcs.fderiv (𝕜 := ℝ)).norm
    obtain ⟨D, hD⟩ := (WeightedSobolev.continuous_gradient_of_contDiff hζ).norm.bounded_above_of_compact_support
      hgcs
    exact ⟨D, fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hD x⟩

/-- Convergence of squared `L²` norms of real functions, from convergence of the extended-real
squared errors to the limit. -/
theorem tendsto_integral_sq_of_lintegral_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {u : ℕ → α → ℝ} {u₀ : α → ℝ} (hu : ∀ n, MemLp (u n) 2 μ)
    (hu₀ : MemLp u₀ 2 μ)
    (h : Tendsto (fun n => ∫⁻ x, ‖u n x - u₀ x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, u n x ^ 2 ∂μ) atTop (𝓝 (∫ x, u₀ x ^ 2 ∂μ)) := by
  -- the error `∫ (u n - u₀)²` tends to zero
  have ha : Tendsto (fun n => ∫ x, (u n x - u₀ x) ^ 2 ∂μ) atTop (𝓝 0) :=
    WeightedSobolev.tendsto_integral_sq_of_lintegral (f := fun n x => u n x - u₀ x)
      (fun n => ((hu n).sub hu₀).aestronglyMeasurable) h
  -- the cross term `∫ (u n - u₀) u₀` is at most `√(∫ (u n - u₀)²) √(∫ u₀²)`
  have hcross : Tendsto (fun n => ∫ x, (u n x - u₀ x) * u₀ x ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => Real.sqrt (∫ x, (u n x - u₀ x) ^ 2 ∂μ) *
      Real.sqrt (∫ x, u₀ x ^ 2 ∂μ)) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact WeightedSobolev.abs_integral_mul_le_sqrt ((hu n).sub hu₀) hu₀
    · have hsq := (Real.continuous_sqrt.tendsto 0).comp ha
      rw [Real.sqrt_zero] at hsq
      simpa using hsq.mul_const (Real.sqrt (∫ x, u₀ x ^ 2 ∂μ))
  -- the expansion `u n² = (u n - u₀)² + 2 (u n - u₀) u₀ + u₀²`
  have hexp : ∀ n, ∫ x, u n x ^ 2 ∂μ = ∫ x, (u n x - u₀ x) ^ 2 ∂μ +
      2 * ∫ x, (u n x - u₀ x) * u₀ x ∂μ + ∫ x, u₀ x ^ 2 ∂μ := by
    intro n
    have i1 : Integrable (fun x => (u n x - u₀ x) ^ 2) μ := ((hu n).sub hu₀).integrable_sq
    have i2 : Integrable (fun x => (u n x - u₀ x) * u₀ x) μ :=
      ((hu n).sub hu₀).integrable_mul hu₀
    have i3 : Integrable (fun x => u₀ x ^ 2) μ := hu₀.integrable_sq
    have i12 : Integrable (fun x => (u n x - u₀ x) ^ 2 + 2 * ((u n x - u₀ x) * u₀ x)) μ :=
      i1.add (i2.const_mul 2)
    have hpt : (fun x => u n x ^ 2) = fun x =>
        ((u n x - u₀ x) ^ 2 + 2 * ((u n x - u₀ x) * u₀ x)) + u₀ x ^ 2 := by
      funext x
      ring
    rw [hpt, integral_add i12 i3, integral_add i1 (i2.const_mul 2), integral_const_mul]
  have htarget : Tendsto (fun n => ∫ x, (u n x - u₀ x) ^ 2 ∂μ +
      2 * ∫ x, (u n x - u₀ x) * u₀ x ∂μ + ∫ x, u₀ x ^ 2 ∂μ) atTop
      (𝓝 (0 + 2 * 0 + ∫ x, u₀ x ^ 2 ∂μ)) :=
    ((ha.add (hcross.const_mul 2)).add_const _)
  simp only [zero_add, mul_zero] at htarget
  exact htarget.congr fun n => (hexp n).symm

/-- A smooth function with compact support is `L²` on a finite measure. -/
theorem memLp_two_of_contDiff_hasCompactSupport [MeasurableSpace E] [BorelSpace E]
    {ν : Measure E} [IsFiniteMeasure ν] {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hcs : HasCompactSupport ζ) : MemLp ζ 2 ν := by
  obtain ⟨⟨C, hC⟩, -⟩ := bounded_of_contDiff_hasCompactSupport hζ hcs
  exact MemLp.of_bound (p := 2) hζ.continuous.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- The norm of the gradient of a smooth function with compact support is `L²`. -/
theorem memLp_two_norm_gradient_of_contDiff_hasCompactSupport [MeasurableSpace E] [BorelSpace E]
    {ν : Measure E} [IsFiniteMeasure ν] {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hcs : HasCompactSupport ζ) : MemLp (fun x => ‖gradient ζ x‖) 2 ν := by
  obtain ⟨-, ⟨D, hD⟩⟩ := bounded_of_contDiff_hasCompactSupport hζ hcs
  exact MemLp.of_bound (p := 2)
    (WeightedSobolev.continuous_gradient_of_contDiff hζ).norm.aestronglyMeasurable D
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hD x)

/-- **Logarithmic Sobolev inequality on the weighted `H¹` space.** Let `ν = f γ_Ω^w` be the
probability of the conditioning theorems, and let `U` satisfy `x ∈ closure U` for
`ν`-almost every `x`. For every pair `(F, G)` in `IsWeightedH1 ν U`, the function `F²` has
integrable entropy and `Ent_ν(F²) ≤ 2w ∫ ‖G‖² dν`. The only external hypothesis is
`hBE : External.BakryEmery`. -/
theorem logSobolev_conditioning_H1 (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    (hΩpos : 0 < ∫ x in Ω, Real.exp (-((2*w)⁻¹ * ‖x‖^2)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = ((volume.restrict Ω).withDensity (fun x => ENNReal.ofReal
      (Real.exp (-((2*w)⁻¹ * ‖x‖^2)) / ∫ y in Ω, Real.exp (-((2*w)⁻¹ * ‖y‖^2))))).withDensity
      (fun x => ENNReal.ofReal (f x)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : ∀ᵐ x ∂ν, x ∈ closure U)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hFG : WeightedSobolev.IsWeightedH1 ν U F G) :
    ∃ (_ : Integrable (fun x => F x ^ 2) ν)
      (_ : Integrable (fun x => Real.negMulLog (F x ^ 2)) ν)
      (_ : Integrable (fun x => ‖G x‖ ^ 2) ν),
      -(∫ x, Real.negMulLog (F x ^ 2) ∂ν) + Real.negMulLog (∫ x, F x ^ 2 ∂ν) ≤
        2 * w * ∫ x, ‖G x‖ ^ 2 ∂ν := by
  have hF : MemLp F 2 ν := hFG.memLp_fun
  have hG : MemLp G 2 ν := hFG.memLp_grad
  -- smooth compactly supported approximants with weighted `H¹` error below `1 / n`
  choose ζ hζC hζcs hζerr using fun n : ℕ =>
    WeightedSobolev.exists_hasCompactSupport_close hU hFG (ε := (n : ENNReal)⁻¹)
      (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
  have hD : Tendsto (fun n : ℕ => ∫⁻ x, ‖ζ n x - F x‖ₑ ^ 2 ∂ν +
      ∫⁻ x, ‖gradient (ζ n) x - G x‖ₑ ^ 2 ∂ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun n => zero_le) fun n => (hζerr n).le
  have hE1 : Tendsto (fun n : ℕ => ∫⁻ x, ‖ζ n x - F x‖ₑ ^ 2 ∂ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD (fun n => zero_le)
      fun n => le_self_add
  have hE2 : Tendsto (fun n : ℕ => ∫⁻ x, ‖gradient (ζ n) x - G x‖ₑ ^ 2 ∂ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD (fun n => zero_le)
      fun n => le_add_self
  -- the entropy inequality for each approximant, from the smooth theorem
  have hLSI : ∀ n, ∃ (_ : Integrable (fun x => ζ n x ^ 2) ν)
      (_ : Integrable (fun x => Real.negMulLog (ζ n x ^ 2)) ν)
      (_ : Integrable (fun x => ‖gradient (ζ n) x‖ ^ 2) ν),
      -(∫ x, Real.negMulLog (ζ n x ^ 2) ∂ν) + Real.negMulLog (∫ x, ζ n x ^ 2 ∂ν) ≤
        2 * w * ∫ x, ‖gradient (ζ n) x‖ ^ 2 ∂ν := by
    intro n
    obtain ⟨hb, hgb⟩ := bounded_of_contDiff_hasCompactSupport (hζC n) (hζcs n)
    exact logSobolev_conditioning_smooth hBE hd hw hΩ hΩm hΩpos hf hf0 hlog ν hν
      ((hζC n).of_le (by simp)) hb hgb
  -- convergence of the squared norms of the approximants
  have hm : Tendsto (fun n => ∫ x, ζ n x ^ 2 ∂ν) atTop (𝓝 (∫ x, F x ^ 2 ∂ν)) :=
    tendsto_integral_sq_of_lintegral_sub (u := fun n x => ζ n x) (u₀ := F)
      (fun n => memLp_two_of_contDiff_hasCompactSupport (hζC n) (hζcs n)) hF hE1
  have hg : Tendsto (fun n => ∫ x, ‖gradient (ζ n) x‖ ^ 2 ∂ν) atTop
      (𝓝 (∫ x, ‖G x‖ ^ 2 ∂ν)) := by
    refine tendsto_integral_sq_of_lintegral_sub (u := fun n x => ‖gradient (ζ n) x‖)
      (u₀ := fun x => ‖G x‖)
      (fun n => memLp_two_norm_gradient_of_contDiff_hasCompactSupport (hζC n) (hζcs n))
      hG.norm ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE2 (fun n => zero_le)
      fun n => lintegral_mono fun x => ?_
    have h1 : ‖‖gradient (ζ n) x‖ - ‖G x‖‖ₑ ≤ ‖gradient (ζ n) x - G x‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (abs_norm_sub_norm_le _ _)
    exact pow_le_pow_left₀ zero_le h1 2
  -- an almost everywhere convergent subsequence
  have hL2 : Tendsto (fun n => eLpNorm (fun x => ζ n x - F x) 2 ν) atTop (𝓝 0) := by
    have hcont : Tendsto (fun n => (∫⁻ x, ‖ζ n x - F x‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ)) atTop
        (𝓝 ((0 : ENNReal) ^ (1 / 2 : ℝ))) :=
      ((ENNReal.continuous_rpow_const).tendsto _).comp hE1
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hcont
    refine hcont.congr fun n => ?_
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun x => ζ n x - F x) (p := 2)
      (by norm_num) (by norm_num) (((hζC n).continuous.aestronglyMeasurable).sub
        hF.aestronglyMeasurable)]
    simp
  have hconv : TendstoInMeasure ν (fun n x => ζ n x) atTop F :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hL2
  obtain ⟨ns, hns, hae⟩ := hconv.exists_seq_tendsto_ae
  -- the entropy bound along the subsequence, and its limit
  have hB : ∀ n, ∫ x, ζ n x ^ 2 * Real.log (ζ n x ^ 2) ∂ν ≤
      2 * w * (∫ x, ‖gradient (ζ n) x‖ ^ 2 ∂ν) - Real.negMulLog (∫ x, ζ n x ^ 2 ∂ν) := by
    intro n
    obtain ⟨-, -, -, hineq⟩ := hLSI n
    have hneg : ∫ x, ζ n x ^ 2 * Real.log (ζ n x ^ 2) ∂ν =
        -∫ x, Real.negMulLog (ζ n x ^ 2) ∂ν := by
      rw [← integral_neg]
      congr 1
      funext x
      simp [Real.negMulLog]
    linarith [hineq, hneg]
  have hBT : Tendsto (fun n => 2 * w * (∫ x, ‖gradient (ζ n) x‖ ^ 2 ∂ν) -
      Real.negMulLog (∫ x, ζ n x ^ 2 ∂ν)) atTop
      (𝓝 (2 * w * (∫ x, ‖G x‖ ^ 2 ∂ν) - Real.negMulLog (∫ x, F x ^ 2 ∂ν))) :=
    (hg.const_mul (2 * w)).sub ((Real.continuous_negMulLog.tendsto _).comp hm)
  -- Fatou's lemma along the subsequence
  have hintζ : ∀ n, Integrable (fun x => ζ n x ^ 2 * Real.log (ζ n x ^ 2)) ν := by
    intro n
    obtain ⟨-, hnm, -, -⟩ := hLSI n
    exact hnm.neg.congr (Eventually.of_forall fun x => by simp [Real.negMulLog])
  obtain ⟨hintL, hleT⟩ := WeightedSobolev.integrable_mul_log_and_le_of_tendsto_ae (μ := ν)
    (h := fun j x => ζ (ns j) x ^ 2) (h₀ := fun x => F x ^ 2)
    (fun j => ((hζC (ns j)).continuous.pow 2).measurable)
    (hF.aemeasurable.pow_const 2)
    (fun j x => sq_nonneg _) (fun x => sq_nonneg _)
    (fun j => hintζ (ns j))
    (by filter_upwards [hae] with x hx using hx.pow 2)
    (fun j => hB (ns j))
    (hBT.comp hns.tendsto_atTop)
  -- integrability of the three terms and the inequality for `F`
  have hIntF2 : Integrable (fun x => F x ^ 2) ν := hF.integrable_sq
  have hIntG : Integrable (fun x => ‖G x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG
  have hnegF : Integrable (fun x => Real.negMulLog (F x ^ 2)) ν :=
    hintL.neg.congr (Eventually.of_forall fun x => by simp [Real.negMulLog])
  refine ⟨hIntF2, hnegF, hIntG, ?_⟩
  have hnegint : ∫ x, Real.negMulLog (F x ^ 2) ∂ν = -∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂ν := by
    rw [← integral_neg]
    congr 1
    funext x
    simp [Real.negMulLog]
  rw [hnegint, neg_neg]
  linarith [hleT]

end Riesz1.LogSobolevEntropy

end

end
