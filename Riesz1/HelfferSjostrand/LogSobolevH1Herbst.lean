/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevHerbstH1Unbounded
public import Riesz1.ToMathlib.WeightedSobolev.LipschitzVersion
public import Riesz1.ToMathlib.WeightedSobolev.Completion

/-!
# Herbst bound for `H¹` observables

This file proves the `H¹` form of the Herbst bound in Lemma 3.8 (second display). Let
`ν = f γ_Ω^w` be the probability of the conditioning theorems, and let `U` be a set whose
closure contains the interior `T` of the positive support of `f` in `Ω`. For every pair
`(F, G)` in the weighted Sobolev space `IsWeightedH1 ν U F G` with `‖G‖ ≤ L` `ν`-almost
everywhere, every real `t` makes `exp (t F)` integrable and gives
`log E_ν e^{tF} ≤ t E_ν F + (w/2) t² L²`.

The proof has three steps. The density of `ν` is continuous and positive on `T`, so the
approximating smooth functions of `IsWeightedH1` converge in `L¹` on every compact subset of `T`.
Then `exists_lipschitzWith_ae_eq` gives an `L`-Lipschitz representative on `T`, and the
Lipschitz theorem applies to it. The only external hypothesis is `hBE : External.BakryEmery`.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ContDiff

namespace Riesz1

open WeightedSobolev

namespace LogSobolevH1Internal

variable {d : ℕ}

/-- The density of `ν` on `T` is continuous, and positive on the interior `T` of the positive
support of `f` in `Ω`. -/
theorem continuousOn_interior_positive {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hΩ : Convex ℝ Ω)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)) :
    ContinuousOn f (interior {x | x ∈ Ω ∧ 0 < f x}) := by
  have h := (LogSobolevInternal.convexOn_neg_log_positive_support hΩ hlog).continuousOn_interior
  refine (Real.continuous_exp.comp_continuousOn h.neg).congr fun x hx => ?_
  have hpos : 0 < f x := (interior_subset hx).2
  simp only [Function.comp_apply, Pi.neg_apply, neg_neg]
  exact (Real.exp_log hpos).symm

/-- On a compact subset of `T`, the density is bounded below by a positive constant. -/
theorem exists_lower_bound_compact {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {w c : ℝ} (hΩ : Convex ℝ Ω)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    (hc : 0 < c) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hKT : K ⊆ interior {x | x ∈ Ω ∧ 0 < f x}) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ c * (f x * Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2))) := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun x hx => by simp [hKe] at hx⟩
  have hcont : ContinuousOn (fun x => c * (f x * Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2))))
      (interior {x | x ∈ Ω ∧ 0 < f x}) :=
    ((continuousOn_interior_positive hΩ hlog).mul (by fun_prop)).const_smul c
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne (hcont.mono hKT)
  have hpos : 0 < c * (f x₀ * Real.exp (-((2 * w)⁻¹ * ‖x₀‖ ^ 2))) :=
    mul_pos hc (mul_pos ((interior_subset (hKT hx₀K)).2) (Real.exp_pos _))
  exact ⟨_, hpos, fun x hx => hmin hx⟩

/-- **Domination of the density on a compact set.** If `ν` has density `ρ` and `m` lower-bounds
`ρ` on `K`, then the lower integral over `K` against Lebesgue measure is dominated by the lower
integral against `ν`. -/
theorem ofReal_mul_lintegral_restrict_le {T K : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {w c m : ℝ} (hf : Measurable f) (hTm : MeasurableSet T)
    (hKm : MeasurableSet K) (hKT : K ⊆ T) (hm : ∀ x ∈ K, m ≤ c * (f x *
      Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2))))
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ENNReal.ofReal m * ∫⁻ x in K, g x ∂volume ≤
      ∫⁻ x, g x ∂(volume.withDensity (fun x => ENNReal.ofReal
        (c * T.indicator (fun y => f y * Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) x))) := by
  have hρm : Measurable (fun x => ENNReal.ofReal
      (c * T.indicator (fun y => f y * Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((hf.mul (by fun_prop)).indicator hTm))
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hρm
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) g, ← lintegral_indicator hKm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ K
  · have hρ : ENNReal.ofReal m ≤ ENNReal.ofReal
        (c * T.indicator (fun y => f y * Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) x) :=
      ENNReal.ofReal_le_ofReal (by rw [indicator_of_mem (hKT hx)]; exact hm x hx)
    rw [indicator_of_mem hx, Pi.mul_apply]
    gcongr
  · rw [indicator_of_notMem hx]
    simp

/-- **Measure domination on a compact set.** Lebesgue measure restricted to `K` is at most
`(ofReal m)⁻¹` times `ν`, when `ν` dominates `ofReal m` times it on `K`. -/
theorem restrict_le_inv_smul {ν : Measure (EuclideanSpace ℝ (Fin d))}
    {K : Set (EuclideanSpace ℝ (Fin d))} {m : ℝ} (hm : 0 < m)
    (hdom : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      ENNReal.ofReal m * ∫⁻ x in K, g x ∂volume ≤ ∫⁻ x, g x ∂ν) :
    volume.restrict K ≤ (ENNReal.ofReal m)⁻¹ • ν := by
  refine Measure.le_iff.mpr fun A hA => ?_
  have h := hdom (A.indicator 1)
  rw [lintegral_indicator_one hA, lintegral_indicator_one hA] at h
  rw [Measure.smul_apply, smul_eq_mul]
  have h0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr hm).ne'
  calc volume.restrict K A = (ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal m * volume.restrict K A) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal m)⁻¹ * ν A := by gcongr

/-- An `L²(ν)` function is `L²` on each compact set of the domination. -/
theorem memLp_restrict_of_domination {V : Type*} [NormedAddCommGroup V]
    {ν : Measure (EuclideanSpace ℝ (Fin d))}
    {K : Set (EuclideanSpace ℝ (Fin d))} {m : ℝ} (hm : 0 < m)
    (hdom : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      ENNReal.ofReal m * ∫⁻ x in K, g x ∂volume ≤ ∫⁻ x, g x ∂ν)
    {F : EuclideanSpace ℝ (Fin d) → V} (hF : MemLp F 2 ν) :
    MemLp F 2 (volume.restrict K) :=
  MemLp.of_measure_le_smul (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hm).ne')
    (restrict_le_inv_smul hm hdom) hF

/-- **`L²` to `L¹` on a compact set.** If the `L²(ν)` distances of `h k` to zero tend to zero,
then the lower `L¹` distances on `K` tend to zero. -/
theorem tendsto_lintegral_enorm_restrict {V : Type*} [NormedAddCommGroup V]
    {ν : Measure (EuclideanSpace ℝ (Fin d))}
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) {m : ℝ} (hm : 0 < m)
    (hdom : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      ENNReal.ofReal m * ∫⁻ x in K, g x ∂volume ≤ ∫⁻ x, g x ∂ν)
    {h : ℕ → EuclideanSpace ℝ (Fin d) → V}
    (hmeas : ∀ k, AEStronglyMeasurable (h k) (volume.restrict K))
    (hL2 : Tendsto (fun k => ∫⁻ x, ‖h k x‖ₑ ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ x in K, ‖h k x‖ₑ ∂volume) atTop (𝓝 0) := by
  have hm0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr hm).ne'
  have hinv : (ENNReal.ofReal m)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hm0
  -- The `L²` lower integrals on `K` tend to zero.
  have hA : Tendsto (fun k => ∫⁻ x in K, ‖h k x‖ₑ ^ 2 ∂volume) atTop (𝓝 0) := by
    have hb : Tendsto (fun k => (ENNReal.ofReal m)⁻¹ * ∫⁻ x, ‖h k x‖ₑ ^ 2 ∂ν) atTop
        (𝓝 ((ENNReal.ofReal m)⁻¹ * 0)) :=
      ENNReal.Tendsto.const_mul hL2 (Or.inr hinv)
    rw [mul_zero] at hb
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun _ => zero_le) fun k => ?_
    have hk := hdom fun x => ‖h k x‖ₑ ^ 2
    calc ∫⁻ x in K, ‖h k x‖ₑ ^ 2 ∂volume
        = (ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal m * ∫⁻ x in K, ‖h k x‖ₑ ^ 2 ∂volume) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hm0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal m)⁻¹ * ∫⁻ x, ‖h k x‖ₑ ^ 2 ∂ν := by gcongr
  -- Hölder's inequality with exponents `2` and `2`, against the constant `1`.
  have hH : ∀ k, ∫⁻ x in K, ‖h k x‖ₑ ∂volume ≤
      (∫⁻ x in K, ‖h k x‖ₑ ^ 2 ∂volume) ^ (1 / 2 : ℝ) * (volume K) ^ (1 / 2 : ℝ) := by
    intro k
    have hf : AEMeasurable (fun x => ‖h k x‖ₑ) (volume.restrict K) :=
      (hmeas k).enorm
    have hg : AEMeasurable (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ≥0∞)) (volume.restrict K) :=
      aemeasurable_const
    have H := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict K) Real.HolderConjugate.two_two
      hf hg
    simpa [Pi.mul_apply, ENNReal.rpow_two, Measure.restrict_apply_univ] using H
  have hpow : Tendsto (fun k => (∫⁻ x in K, ‖h k x‖ₑ ^ 2 ∂volume) ^ (1 / 2 : ℝ)) atTop
      (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
    ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp hA
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hpow
  have hbd : Tendsto (fun k => (∫⁻ x in K, ‖h k x‖ₑ ^ 2 ∂volume) ^ (1 / 2 : ℝ) *
      (volume K) ^ (1 / 2 : ℝ)) atTop (𝓝 (0 * (volume K) ^ (1 / 2 : ℝ))) :=
    ENNReal.Tendsto.mul_const hpow
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.measure_lt_top.ne))
  rw [zero_mul] at hbd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbd
    (fun _ => zero_le) hH

/-- The real `L¹` distances on `K` tend to zero, from their lower integrals. -/
theorem tendsto_integral_norm_restrict {V : Type*} [NormedAddCommGroup V]
    {K : Set (EuclideanSpace ℝ (Fin d))} {h : ℕ → EuclideanSpace ℝ (Fin d) → V}
    (hmeas : ∀ k, AEStronglyMeasurable (h k) (volume.restrict K))
    (hI : Tendsto (fun k => ∫⁻ x in K, ‖h k x‖ₑ ∂volume) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in K, ‖h k x‖ ∂volume) atTop (𝓝 0) := by
  have hr : ∀ k, ∫ x in K, ‖h k x‖ ∂volume = (∫⁻ x in K, ‖h k x‖ₑ ∂volume).toReal :=
    fun k => integral_norm_eq_lintegral_enorm (hmeas k)
  simp_rw [hr]
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hI
  rw [ENNReal.toReal_zero] at hlim
  exact hlim

end LogSobolevH1Internal

open LogSobolevH1Internal

/-- **Herbst bound for `H¹` observables.** Let `ν = f γ_Ω^w` be the probability of the
conditioning theorems, and let `U` have closure containing the interior `T` of the positive
support of `f` in `Ω`. For every pair `(F, G)` in `IsWeightedH1 ν U F G` with `‖G‖ ≤ L`
`ν`-almost everywhere, and every real `t`, the function `exp (t F)` is `ν`-integrable and
`log E_ν e^{tF} ≤ t E_ν F + (w/2) t² L²`. This is the `H¹` form of the second display of
Lemma 3.8. -/
theorem logSobolev_conditioning_herbst_H1 (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    {c : ℝ} (hc : 0 < c) (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) x)))
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : interior {x | x ∈ Ω ∧ 0 < f x} ⊆ closure U)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hFG : WeightedSobolev.IsWeightedH1 ν U F G)
    {L : ℝ} (hL : ∀ᵐ x ∂ν, ‖G x‖ ≤ L) (t : ℝ) :
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * F x)) ν ∧
      Real.log (∫ x, Real.exp (t * F x) ∂ν) ≤ t * ∫ x, F x ∂ν + w / 2 * t ^ 2 * L ^ 2 := by
  classical
  have hFm : MemLp F 2 ν := hFG.memLp_fun
  have hGm : MemLp G 2 ν := hFG.memLp_grad
  obtain ⟨φ, hφS, hφ1, hφ2⟩ := hFG.2.2
  -- The positive support `S` of `f` in `Ω`, and its interior `T`.
  have hSc : Convex ℝ {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} :=
    LogSobolevInternal.convex_positive_support hΩ hlog
  have hnull : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      x ∉ frontier {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} :=
    ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hSc.addHaar_frontier volume)
  have hTm : MeasurableSet (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}) :=
    isOpen_interior.measurableSet
  have hTc : Convex ℝ (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}) :=
    hSc.interior
  have hTΩ : interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} ⊆ Ω :=
    fun x hx => (interior_subset hx).1
  have hTpos : ∀ x ∈ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}, 0 < f x :=
    fun x hx => (interior_subset hx).2
  -- Off `T`, the density over `Ω` vanishes almost everywhere, so `ν` lives on `T`.
  have hr_ae : (fun x => ENNReal.ofReal (c * Ω.indicator (fun y => f y *
      Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) x)) =ᵐ[volume]
      (fun x => ENNReal.ofReal (c *
        (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}).indicator
          (fun y => f y * Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) x)) := by
    filter_upwards [hnull] with x hx
    by_cases hxT : x ∈ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}
    · rw [indicator_of_mem hxT, indicator_of_mem (hTΩ hxT)]
    · by_cases hxΩ : x ∈ Ω
      · have hfx : f x = 0 := by
          by_contra hne
          have hpos : 0 < f x := lt_of_le_of_ne (hf0 x hxΩ) (Ne.symm hne)
          exact hx ⟨subset_closure ⟨hxΩ, hpos⟩, hxT⟩
        rw [indicator_of_mem hxΩ, indicator_of_notMem hxT, hfx]
        simp
      · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxT]
  have hν_T : ν = volume.withDensity (fun x => ENNReal.ofReal (c *
      (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}).indicator
        (fun y => f y * Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) x)) :=
    hν.trans (withDensity_congr_ae hr_ae)
  have hρm : Measurable (fun x => ENNReal.ofReal (c *
      (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}).indicator
        (fun y => f y * Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((hf.mul (by fun_prop)).indicator hTm))
  -- Domination of `ν` by Lebesgue measure on each compact subset of `T`.
  have hdom : ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      K ⊆ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} →
      ∃ m : ℝ, 0 < m ∧ ∀ g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        ENNReal.ofReal m * ∫⁻ x in K, g x ∂volume ≤ ∫⁻ x, g x ∂ν := by
    intro K hK hKT
    obtain ⟨m, hm, hmK⟩ := LogSobolevH1Internal.exists_lower_bound_compact hΩ hlog hc hK hKT
    refine ⟨m, hm, fun g => ?_⟩
    rw [hν_T]
    exact LogSobolevH1Internal.ofReal_mul_lintegral_restrict_le hf hTm hK.measurableSet hKT hmK g
  -- The approximants are `C¹` on open sets containing `T`.
  have hφT : ∀ k, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧
      interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} ⊆ W ∧
        ContDiffOn ℝ 1 (φ k) W := by
    intro k
    obtain ⟨W, hW, hUW, hC⟩ := hφS k
    exact ⟨W, hW, hU.trans hUW, hC.of_le (by exact_mod_cast le_top)⟩
  -- `L¹` statements on compact subsets of `T`.
  have hFloc : ∀ K ⊆ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x},
      IsCompact K → IntegrableOn F K volume := by
    intro K hKT hK
    obtain ⟨m, hm, hdomK⟩ := hdom K hK hKT
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact (memLp_restrict_of_domination hm hdomK hFm).integrable one_le_two
  have hGloc : ∀ K ⊆ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x},
      IsCompact K → IntegrableOn G K volume := by
    intro K hKT hK
    obtain ⟨m, hm, hdomK⟩ := hdom K hK hKT
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact (memLp_restrict_of_domination hm hdomK hGm).integrable one_le_two
  have hF1 : ∀ K ⊆ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x},
      IsCompact K → Tendsto (fun k => ∫ x in K, |φ k x - F x|) atTop (𝓝 0) := by
    intro K hKT hK
    obtain ⟨m, hm, hdomK⟩ := hdom K hK hKT
    have hmeas : ∀ k, AEStronglyMeasurable (fun x => φ k x - F x) (volume.restrict K) := by
      intro k
      obtain ⟨W, _, hTW, hφW⟩ := hφT k
      exact ((hφW.continuousOn.mono (hKT.trans hTW)).aestronglyMeasurable hK.measurableSet).sub
        (memLp_restrict_of_domination hm hdomK hFm).aestronglyMeasurable
    have hI := tendsto_lintegral_enorm_restrict hK hm hdomK
      (h := fun k x => φ k x - F x) hmeas hφ1
    have := tendsto_integral_norm_restrict (h := fun k x => φ k x - F x) hmeas hI
    simpa only [Real.norm_eq_abs] using this
  have hG1 : ∀ K ⊆ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x},
      IsCompact K → Tendsto (fun k => ∫ x in K, ‖gradient (φ k) x - G x‖) atTop (𝓝 0) := by
    intro K hKT hK
    obtain ⟨m, hm, hdomK⟩ := hdom K hK hKT
    have hmeas : ∀ k, AEStronglyMeasurable (fun x => gradient (φ k) x - G x)
        (volume.restrict K) := by
      intro k
      obtain ⟨W, hW, hTW, hφW⟩ := hφT k
      have hgrad : ContinuousOn (fun x => gradient (φ k) x) W :=
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp_continuousOn
          (hφW.continuousOn_fderiv_of_isOpen hW le_rfl)
      exact ((hgrad.mono (hKT.trans hTW)).aestronglyMeasurable hK.measurableSet).sub
        (memLp_restrict_of_domination hm hdomK hGm).aestronglyMeasurable
    have hI := tendsto_lintegral_enorm_restrict hK hm hdomK
      (h := fun k x => gradient (φ k) x - G x) hmeas hφ2
    exact tendsto_integral_norm_restrict (h := fun k x => gradient (φ k) x - G x) hmeas hI
  -- The bound of `G` on `T`, almost everywhere for Lebesgue measure.
  have hL0 : 0 ≤ L := by
    obtain ⟨x, hx⟩ := hL.exists
    exact (norm_nonneg _).trans hx
  have hGT : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      x ∈ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} →
        ‖G x‖ ≤ (Real.toNNReal L : ℝ) := by
    have hν' := hL
    rw [hν_T, ae_withDensity_iff hρm] at hν'
    filter_upwards [hν'] with x hx hxT
    rw [Real.coe_toNNReal L hL0]
    apply hx
    rw [indicator_of_mem hxT]
    exact (ENNReal.ofReal_pos.mpr (mul_pos hc (mul_pos (hTpos x hxT) (Real.exp_pos _)))).ne'
  -- The Lipschitz representative of `F` on `T`.
  obtain ⟨g, hgL, hgeq⟩ := WeightedSobolev.exists_lipschitzWith_ae_eq isOpen_interior hTc
    hφT hFloc hGloc hF1 hG1 hGT
  -- `g = F` almost surely for `ν`, since `ν` lives on `T`.
  have hgν : ∀ᵐ x ∂ν, g x = F x := by
    rw [hν_T, ae_withDensity_iff hρm]
    filter_upwards [hgeq] with x hx hρx
    have hxT : x ∈ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} := by
      by_contra hxT
      apply hρx
      rw [indicator_of_notMem hxT, mul_zero, ENNReal.ofReal_zero]
    exact hx hxT
  -- The Herbst bound on `T`, applied to the Lipschitz representative `g`.
  have hgT : LipschitzOnWith (Real.toNNReal L) g
      (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}) :=
    hgL.lipschitzOnWith
  obtain ⟨hgint, hgexp, hgbound⟩ := logSobolev_conditioning_density_herbst_lipschitz hBE hd hw
    hTc hTm hf (fun x hx => hf0 x (hTΩ hx))
    (fun x hx y hy s h0 h1 => hlog x (hTΩ hx) y (hTΩ hy) s h0 h1) hc ν hν_T hgT t
  have hexp : (fun x => Real.exp (t * g x)) =ᵐ[ν] (fun x => Real.exp (t * F x)) :=
    hgν.mono fun x hx => by simp only [hx]
  have e1 : ∫ x, Real.exp (t * F x) ∂ν = ∫ x, Real.exp (t * g x) ∂ν :=
    (integral_congr_ae hexp).symm
  have e2 : ∫ x, F x ∂ν = ∫ x, g x ∂ν := (integral_congr_ae hgν).symm
  rw [Real.coe_toNNReal L hL0] at hgbound
  rw [e1, e2]
  exact ⟨hgint.congr hgν, hgexp.congr hexp, hgbound⟩

end Riesz1

end

end
