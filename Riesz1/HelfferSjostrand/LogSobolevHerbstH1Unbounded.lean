/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevHerbstH1Moments
public import Riesz1.HelfferSjostrand.LogSobolevConditioningHerbst
public import Riesz1.ToMathlib.WeightedSobolev.LipschitzClip

/-!
# Herbst bound for unbounded Lipschitz observables under convex conditioning

The bounded Herbst bound of `Riesz1.logSobolev_conditioning_herbst_bounded` needs a bound on the
observable. Here the bound is removed for observables that are Lipschitz on the conditioning
domain `Ω`. Such an observable has linear growth on `Ω`, and every exponential moment of `‖x‖`
is finite under `ν` (see `LogSobolevInternal.integrable_exp_mul_norm`). The observable is clipped
at level `n`, the bounded bound applies to each clipped observable, and dominated convergence
passes to the limit `n → ∞`.

The `H¹` version of Lemma 3.8, for every `F` in the weighted Sobolev space with
`‖∇F‖ ≤ L` almost everywhere, is not proved here. It needs that such an `F` is Lipschitz on `Ω`
almost everywhere, which is not formalized.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff

namespace Riesz1.LogSobolevInternal

/-- A measure of density `c 1_Ω f γ` is concentrated on `Ω`. -/
lemma ae_mem_of_density {d : ℕ} {w : ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {c : ℝ}
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x))) :
    ∀ᵐ x ∂ν, x ∈ Ω := by
  have hρ : Measurable (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((hf.mul (by fun_prop)).indicator hΩm))
  rw [hν, ae_withDensity_iff hρ]
  refine Eventually.of_forall fun x hx => ?_
  by_contra hxΩ
  apply hx
  simp [indicator_of_notMem hxΩ]

/-- A function continuous on `Ω` is almost everywhere strongly measurable for a measure
concentrated on `Ω`. -/
lemma aestronglyMeasurable_of_continuousOn_ae {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContinuousOn g Ω)
    {ν : Measure (EuclideanSpace ℝ (Fin d))} (hΩae : ∀ᵐ x ∂ν, x ∈ Ω) :
    AEStronglyMeasurable g ν := by
  rw [← Measure.restrict_eq_self_of_ae_mem hΩae]
  exact hg.aestronglyMeasurable hΩm

end Riesz1.LogSobolevInternal

namespace Riesz1

open WeightedSobolev

/-- Herbst bound for a bounded observable which is Lipschitz on the conditioning domain `Ω`.
Only the bound on `Ω` and the Lipschitz condition on `Ω` are used. -/
theorem logSobolev_conditioning_density_herbst_lipschitz_bounded (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    {c : ℝ} (hc : 0 < c) (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)))
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {K : NNReal} (hFL : LipschitzOnWith K F Ω)
    {C : ℝ} (hFb : ∀ x ∈ Ω, |F x| ≤ C) (t : ℝ) :
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * F x)) ν ∧
      Real.log (∫ x, Real.exp (t * F x) ∂ν) ≤
        t * ∫ x, F x ∂ν + w / 2 * t ^ 2 * (K : ℝ) ^ 2 := by
  classical
  have hΩae : ∀ᵐ x ∂ν, x ∈ Ω := LogSobolevInternal.ae_mem_of_density hΩm hf ν hν
  obtain ⟨x₀, hx₀⟩ := hΩae.exists
  have hC0 : 0 ≤ C := (abs_nonneg (F x₀)).trans (hFb x₀ hx₀)
  obtain ⟨G₀, hG₀, heq⟩ := hFL.extend_real
  let G := fun x => max (-C) (min C (G₀ x))
  have hG : LipschitzWith K G := (hG₀.const_min C).const_max (-C)
  have hGb : ∀ x, |G x| ≤ C := by
    intro x
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hFG : F =ᵐ[ν] G := by
    filter_upwards [hΩae] with x hx
    dsimp [G]
    rw [← heq hx, min_eq_right (abs_le.mp (hFb x hx)).2,
      max_eq_right (abs_le.mp (hFb x hx)).1]
  have hE : (fun x => Real.exp (t * F x)) =ᵐ[ν] (fun x => Real.exp (t * G x)) :=
    hFG.mono (fun _ hx => congrArg (fun r => Real.exp (t * r)) hx)
  refine ⟨(herbst_integrable_of_bounded hG.continuous hGb).congr hFG.symm,
    (herbst_integrable_exp hG.continuous hGb t).congr hE.symm, ?_⟩
  rw [integral_congr_ae hFG, integral_congr_ae hE]
  apply LogSobolevInternal.herbst_bounded_lipschitz_of_lsi ν hw _ hG hGb t
  intro q hq hqb ⟨D, hD⟩
  obtain ⟨_, _, _, he⟩ := logSobolev_conditioning_density_smooth hBE hd hw hΩ hf0 hlog hc ν hν
    hq hqb ⟨D, fun x => by rw [LogSobolevInternal.norm_gradient_eq_norm_fderiv]; exact hD x⟩
  simpa only [Real.negMulLog_eq_neg, integral_neg, neg_neg,
    LogSobolevInternal.norm_gradient_eq_norm_fderiv, sub_eq_add_neg] using he

end Riesz1

namespace Riesz1

open WeightedSobolev

/-- Herbst bound for an observable which is Lipschitz on the conditioning domain `Ω`, with no
bound on its values. Its exponential moments are finite because `ν` has all exponential moments
of `‖x‖`. -/
theorem logSobolev_conditioning_density_herbst_lipschitz (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    {c : ℝ} (hc : 0 < c) (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)))
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {K : NNReal} (hFL : LipschitzOnWith K F Ω) (t : ℝ) :
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * F x)) ν ∧
      Real.log (∫ x, Real.exp (t * F x) ∂ν) ≤
        t * ∫ x, F x ∂ν + w / 2 * t ^ 2 * (K : ℝ) ^ 2 := by
  classical
  have hΩae : ∀ᵐ x ∂ν, x ∈ Ω := LogSobolevInternal.ae_mem_of_density hΩm hf ν hν
  obtain ⟨x₀, hx₀⟩ := hΩae.exists
  -- Every exponential moment of `‖x‖` is finite under `ν`.
  have hmom : ∀ s : ℝ, Integrable (fun x => Real.exp (s * ‖x‖)) ν :=
    fun s => LogSobolevInternal.integrable_exp_mul_norm hw hΩ hΩm hf hf0 hlog hc ν hν s
  -- Linear growth of `F` on `Ω`, from the Lipschitz bound and the point `x₀`.
  set A : ℝ := |F x₀| + K * ‖x₀‖ with hA
  have hgrowth : ∀ x ∈ Ω, |F x| ≤ A + K * ‖x‖ := by
    intro x hx
    have h1 : |F x - F x₀| ≤ K * ‖x‖ + K * ‖x₀‖ := by
      have hdist := hFL.dist_le_mul x hx x₀ hx₀
      rw [Real.dist_eq, dist_eq_norm] at hdist
      calc |F x - F x₀| ≤ K * ‖x - x₀‖ := hdist
        _ ≤ K * (‖x‖ + ‖x₀‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (NNReal.coe_nonneg K)
        _ = K * ‖x‖ + K * ‖x₀‖ := by ring
    have h2 := abs_add_le (F x - F x₀) (F x₀)
    rw [sub_add_cancel] at h2
    rw [hA]
    linarith
  have hnorm : Integrable (fun x => ‖x‖) ν := by
    refine Integrable.mono' (hmom 1) measurable_norm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg x), one_mul]
    linarith [Real.add_one_le_exp ‖x‖, norm_nonneg x]
  have hbd : Integrable (fun x => A + K * ‖x‖) ν :=
    (integrable_const A).add (hnorm.const_mul (K : ℝ))
  have hFint : Integrable F ν := by
    refine Integrable.mono' hbd
      (LogSobolevInternal.aestronglyMeasurable_of_continuousOn_ae hΩm hFL.continuousOn hΩae)
      ?_
    filter_upwards [hΩae] with x hx
    rw [Real.norm_eq_abs]
    exact hgrowth x hx
  -- The dominating function for every tilt `t`.
  have hdom_int : ∀ t : ℝ, Integrable (fun x => Real.exp (|t| * (A + K * ‖x‖))) ν := by
    intro t
    refine ((hmom (|t| * K)).const_mul (Real.exp (|t| * A))).congr
      (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * F x)) ν := by
    intro t
    refine Integrable.mono' (hdom_int t)
      (LogSobolevInternal.aestronglyMeasurable_of_continuousOn_ae hΩm
        ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hFL.continuousOn)))
        hΩae) ?_
    filter_upwards [hΩae] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    calc t * F x ≤ |t * F x| := le_abs_self _
      _ = |t| * |F x| := abs_mul _ _
      _ ≤ |t| * (A + K * ‖x‖) := mul_le_mul_of_nonneg_left (hgrowth x hx) (abs_nonneg t)
  -- Clip at level `n`, apply the bounded bound, and let `n → ∞`.
  have hn : ∀ n : ℕ, Integrable (fun x => clipReal (n : ℝ) (F x)) ν ∧
      Integrable (fun x => Real.exp (t * clipReal (n : ℝ) (F x))) ν ∧
      Real.log (∫ x, Real.exp (t * clipReal (n : ℝ) (F x)) ∂ν) ≤
        t * ∫ x, clipReal (n : ℝ) (F x) ∂ν + w / 2 * t ^ 2 * (K : ℝ) ^ 2 := fun n =>
    logSobolev_conditioning_density_herbst_lipschitz_bounded hBE hd hw hΩ hΩm hf hf0 hlog hc ν hν
      (lipschitzOnWith_clipReal hFL n) (C := n)
      (fun x _ => abs_clipReal_le_radius (Nat.cast_nonneg n)) t
  have hmean : Tendsto (fun n : ℕ => ∫ x, clipReal (n : ℝ) (F x) ∂ν) atTop
      (𝓝 (∫ x, F x ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
      (fun n => (hn n).1.aestronglyMeasurable) hFint.norm
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        exact abs_clipReal_le (Nat.cast_nonneg n))
      (Eventually.of_forall fun x => tendsto_clipReal_nat (F x))
  have hexp_lim : Tendsto (fun n : ℕ => ∫ x, Real.exp (t * clipReal (n : ℝ) (F x)) ∂ν) atTop
      (𝓝 (∫ x, Real.exp (t * F x) ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun x => Real.exp (|t| * (A + K * ‖x‖)))
      (fun n => (hn n).2.1.aestronglyMeasurable) (hdom_int t)
      (fun n => by
        filter_upwards [hΩae] with x hx
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        apply Real.exp_le_exp.mpr
        calc t * clipReal (n : ℝ) (F x) ≤ |t * clipReal (n : ℝ) (F x)| := le_abs_self _
          _ = |t| * |clipReal (n : ℝ) (F x)| := abs_mul _ _
          _ ≤ |t| * |F x| :=
            mul_le_mul_of_nonneg_left (abs_clipReal_le (Nat.cast_nonneg n)) (abs_nonneg t)
          _ ≤ |t| * (A + K * ‖x‖) := mul_le_mul_of_nonneg_left (hgrowth x hx) (abs_nonneg t))
      (Eventually.of_forall fun x =>
        (Real.continuous_exp.tendsto (t * F x)).comp ((tendsto_clipReal_nat (F x)).const_mul t))
  have hpos : 0 < ∫ x, Real.exp (t * F x) ∂ν := by
    rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun x => (Real.exp_pos _).le)
      (hexpint t)]
    have hsupp : Function.support (fun x => Real.exp (t * F x)) = Set.univ := by
      ext x
      simp [Real.exp_ne_zero]
    rw [hsupp, measure_univ]
    exact one_pos
  have hlog_lim := (Real.continuousAt_log hpos.ne').tendsto.comp hexp_lim
  have hrhs : Tendsto (fun n : ℕ => t * ∫ x, clipReal (n : ℝ) (F x) ∂ν +
      w / 2 * t ^ 2 * (K : ℝ) ^ 2) atTop
      (𝓝 (t * ∫ x, F x ∂ν + w / 2 * t ^ 2 * (K : ℝ) ^ 2)) :=
    (hmean.const_mul t).add_const _
  exact ⟨hFint, hexpint t,
    le_of_tendsto_of_tendsto hlog_lim hrhs (Eventually.of_forall fun n => (hn n).2.2)⟩

end Riesz1

namespace Riesz1

/-- **Herbst under convex conditioning, Lipschitz observable.** The observable is Lipschitz with
constant `K` on the convex conditioning domain `Ω`, and its values are not bounded. Every real
tilt `t` is allowed. -/
theorem logSobolev_conditioning_herbst_lipschitz (hBE : External.BakryEmery)
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
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {K : NNReal} (hFL : LipschitzOnWith K F Ω) (t : ℝ) :
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * F x)) ν ∧
      Real.log (∫ x, Real.exp (t * F x) ∂ν) ≤
        t * ∫ x, F x ∂ν + w / 2 * t ^ 2 * (K : ℝ) ^ 2 :=
  logSobolev_conditioning_density_herbst_lipschitz hBE hd hw hΩ hΩm hf hf0 hlog
    (inv_pos.mpr hΩpos) ν (hν.trans (LogSobolevInternal.conditioned_density_eq hΩm hf hΩpos))
    hFL t

end Riesz1

namespace Riesz1

open WeightedSobolev

/-- Herbst bound for a `C¹` observable whose gradient is bounded `ν`-almost everywhere, on the
interior `T` of the positive support of `f` in `Ω`. The bound is first shown on `T`, where `ν`
has a positive density, then the Lipschitz theorem applies on `T`. -/
theorem logSobolev_conditioning_density_herbst_ae (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    {c : ℝ} (hc : 0 < c) (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)))
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ContDiff ℝ 1 F)
    {L : ℝ} (hL : ∀ᵐ x ∂ν, ‖gradient F x‖ ≤ L) (t : ℝ) :
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * F x)) ν ∧
      Real.log (∫ x, Real.exp (t * F x) ∂ν) ≤
        t * ∫ x, F x ∂ν + w / 2 * t ^ 2 * L ^ 2 := by
  classical
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
      Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)) =ᵐ[volume]
      (fun x => ENNReal.ofReal (c * (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}).indicator
        (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)) := by
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
        (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)) :=
    hν.trans (withDensity_congr_ae hr_ae)
  -- The gradient bound holds on `T`: the set where it fails is open and `ν`-null, but `ν`
  -- has positive density on `T`, so the set is empty.
  have hgrad_fderiv : ∀ᵐ x ∂ν, ‖fderiv ℝ F x‖ ≤ L := by
    filter_upwards [hL] with x hx
    rwa [LogSobolevInternal.norm_gradient_eq_norm_fderiv] at hx
  have hfcont : Continuous (fun x => ‖fderiv ℝ F x‖) :=
    (hF.continuous_fderiv (by norm_num)).norm
  have hBo : IsOpen (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} ∩
      {x | L < ‖fderiv ℝ F x‖}) :=
    isOpen_interior.inter (isOpen_lt continuous_const hfcont)
  have hBnull : ν (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} ∩
      {x | L < ‖fderiv ℝ F x‖}) = 0 :=
    measure_mono_null (fun x hx => not_le.mpr hx.2) (ae_iff.mp hgrad_fderiv)
  have hBempty : interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} ∩
      {x | L < ‖fderiv ℝ F x‖} = ∅ := by
    by_contra hne
    have hBpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin d)))
        (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} ∩
          {x | L < ‖fderiv ℝ F x‖}) :=
      hBo.measure_pos volume (Set.nonempty_iff_ne_empty.mpr hne)
    have hρ : Measurable (fun x => ENNReal.ofReal (c *
        (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}).indicator
          (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul
        ((hf.mul (by fun_prop)).indicator hTm))
    rw [hν_T, withDensity_apply_eq_zero hρ] at hBnull
    have hset : {x | ENNReal.ofReal (c *
        (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}).indicator
          (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x) ≠ 0} ∩
        (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} ∩
          {x | L < ‖fderiv ℝ F x‖}) =
        interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} ∩
          {x | L < ‖fderiv ℝ F x‖} := by
      ext x
      constructor
      · exact fun h => h.2
      · intro hx
        refine ⟨?_, hx⟩
        have hxT := hx.1
        simp only [Set.mem_ofPred_eq]
        rw [indicator_of_mem hxT, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact mul_pos hc (mul_pos (hTpos x hxT) (Real.exp_pos _))
    rw [hset] at hBnull
    exact hBpos.ne' hBnull
  have hgrad_T : ∀ x ∈ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x},
      ‖fderiv ℝ F x‖ ≤ L := by
    intro x hx
    by_contra hlt
    exact (Set.eq_empty_iff_forall_notMem.mp hBempty) x ⟨hx, not_le.mp hlt⟩
  -- Apply the Lipschitz theorem on `T`, where `ν` is concentrated.
  have hTae : ∀ᵐ x ∂ν, x ∈ interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x} :=
    LogSobolevInternal.ae_mem_of_density hTm hf ν hν_T
  obtain ⟨x₀, hx₀⟩ := hTae.exists
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hgrad_T x₀ hx₀)
  have hFL : LipschitzOnWith ⟨L, hL0⟩ F
      (interior {x : EuclideanSpace ℝ (Fin d) | x ∈ Ω ∧ 0 < f x}) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hF.differentiable one_ne_zero x) _ hTc
    intro x hx
    change ‖fderiv ℝ F x‖₊ ≤ (⟨L, hL0⟩ : ℝ≥0)
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm]
    exact hgrad_T x hx
  exact logSobolev_conditioning_density_herbst_lipschitz hBE hd hw hTc hTm hf
    (fun x hx => hf0 x (hTΩ hx))
    (fun x hx y hy t h0 h1 => hlog x (hTΩ hx) y (hTΩ hy) t h0 h1) hc ν hν_T hFL t

/-- **Herbst under convex conditioning, smooth observable.** The observable is `C¹` and its
gradient is bounded by `L` almost everywhere for `ν`. Its values are not bounded, and every real
tilt `t` is allowed. This is the unbounded form of `Riesz1.logSobolev_conditioning_herbst_bounded`
for smooth observables. -/
theorem logSobolev_conditioning_herbst (hBE : External.BakryEmery)
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
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ContDiff ℝ 1 F)
    {L : ℝ} (hL : ∀ᵐ x ∂ν, ‖gradient F x‖ ≤ L) (t : ℝ) :
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * F x)) ν ∧
      Real.log (∫ x, Real.exp (t * F x) ∂ν) ≤ t * ∫ x, F x ∂ν + w / 2 * t ^ 2 * L ^ 2 :=
  logSobolev_conditioning_density_herbst_ae hBE hd hw hΩ hf hf0 hlog (inv_pos.mpr hΩpos) ν
    (hν.trans (LogSobolevInternal.conditioned_density_eq hΩm hf hΩpos)) hF hL t

end Riesz1

end

end
