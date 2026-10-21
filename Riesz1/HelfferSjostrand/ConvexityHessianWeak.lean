/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.Completion
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Riesz1.ToMathlib.WeightedSobolev.LocalIntegrationByParts
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Weak gradients on a weighted Sobolev completion are classical gradients almost everywhere

Let `ν` be the exponential tilt `(volume.restrict U).tilted (-V)` of Lebesgue measure on an open
set `U`. If `G` is the weak gradient of a function `F` in the completion `IsWeightedH1 ν U F G`,
and `F` is smooth on `U`, then `G` equals the classical gradient of `F` `ν`-almost everywhere.
This holds when `V` is continuous on `U`, which is an extra hypothesis of the main result
`ae_gradient_eq_of_isWeightedH1_of_continuousOn`.

The proof passes the approximating smooth functions to the limit against test functions. The
limit step needs the bound `exp V ∈ L²_loc(U)`, which holds when `V` is continuous on `U`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Riesz1.ConvexityHessian

variable {n : ℕ}

/-! ### Auxiliary `L²` facts -/

section Auxiliary

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A vector-valued function with finite second enorm moment lies in `L²(μ)`. -/
theorem memLp_two_of_lintegral_lt_top {E' : Type*} [NormedAddCommGroup E'] {f : Ω → E'}
    (hf : AEStronglyMeasurable f μ) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ⊤) : MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm hf]
  refine ⟨hf.norm.pow 2, ?_⟩
  simpa only [HasFiniteIntegral, enorm_pow, enorm_norm] using h

/-- The eventual `L²` membership of a sequence whose squared distances to zero tend to zero. -/
theorem eventually_memLp_of_tendsto_lintegral {E' : Type*} [NormedAddCommGroup E'] {f : ℕ → Ω → E'}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (h : Tendsto (fun k => ∫⁻ x, ‖f k x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, MemLp (f k) 2 μ := by
  have hfin : ∀ᶠ k in atTop, ∫⁻ x, ‖f k x‖ₑ ^ 2 ∂μ < ⊤ :=
    (h.eventually (gt_mem_nhds (by norm_num : (0 : ENNReal) < 1))).mono fun k hk =>
      lt_of_lt_of_le hk le_top
  exact hfin.mono fun k hk => memLp_two_of_lintegral_lt_top (hf k) hk

/-- The real inner product with a fixed vector of an `L²` vector field lies in `L²`. -/
theorem memLp_inner_of_memLp {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    {f : Ω → E'} (hf : MemLp f 2 μ) (v : E') : MemLp (fun x => inner ℝ (f x) v) 2 μ := by
  refine MemLp.of_le (hf.norm.const_mul ‖v‖) ?_ ?_
  · exact (continuous_id.inner continuous_const).comp_aestronglyMeasurable hf.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), Real.norm_eq_abs,
      mul_comm]
    exact abs_real_inner_le_norm _ _

/-- The squared real inner products with a fixed vector have eventually finite integrals, and
their integrals tend to zero when the squared norms of the vector fields do. -/
theorem eventually_memLp_and_tendsto_inner {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] {a : ℕ → Ω → E'} (ha : ∀ k, AEStronglyMeasurable (a k) μ)
    (h : Tendsto (fun k => ∫⁻ x, ‖a k x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) (v : E') :
    (∀ᶠ k in atTop, MemLp (fun x => inner ℝ (a k x) v) 2 μ) ∧
      Tendsto (fun k => ∫ x, (inner ℝ (a k x) v) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hmem := eventually_memLp_of_tendsto_lintegral ha h
  have hA := Riesz1.WeightedSobolev.tendsto_integral_norm_sq_of_lintegral ha h
  refine ⟨hmem.mono fun k hk => memLp_inner_of_memLp hk v, ?_⟩
  have hbound : ∀ᶠ k in atTop, ∫ x, (inner ℝ (a k x) v) ^ 2 ∂μ ≤
      ∫ x, ‖v‖ ^ 2 * ‖a k x‖ ^ 2 ∂μ := by
    refine hmem.mono fun k hk => integral_mono_of_nonneg
      (Eventually.of_forall fun x => sq_nonneg _) ?_ (Eventually.of_forall fun x => ?_)
    · exact ((memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).1 hk).const_mul _
    · have h1 := abs_real_inner_le_norm (a k x) v
      have h2 : 0 ≤ ‖a k x‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have h3 := sq_abs (inner ℝ (a k x) v)
      nlinarith [abs_nonneg (inner ℝ (a k x) v)]
  have hupper : Tendsto (fun k => ∫ x, ‖v‖ ^ 2 * ‖a k x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hc : Tendsto (fun k => ‖v‖ ^ 2 * ∫ x, ‖a k x‖ ^ 2 ∂μ) atTop (𝓝 (‖v‖ ^ 2 * 0)) :=
      hA.const_mul _
    rw [mul_zero] at hc
    refine hc.congr fun k => ?_
    rw [integral_const_mul]
  exact squeeze_zero' (Eventually.of_forall fun k => integral_nonneg fun x => sq_nonneg _)
    hbound hupper

end Auxiliary

/-! ### The tilted measure and the integrability of cutoff products -/

section Tilted

/-- The exponential identity `exp(-t) exp(t) = 1`. -/
theorem exp_neg_mul_exp (t : ℝ) : Real.exp (-t) * Real.exp t = 1 := by
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- Integrals against the tilted measure recover the Lebesgue integral on `U` for test functions
supported in `U`. The identity holds for every `g` once `∫_U exp(-V)` is nonzero. -/
theorem integral_mul_eq_integral_tilted {U : Set (EuclideanSpace ℝ (Fin n))}
    {V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hI : ∫ x, Real.exp (-V x) ∂(volume.restrict U) ≠ 0)
    {c : EuclideanSpace ℝ (Fin n) → ℝ} (hcU : tsupport c ⊆ U)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x, c x * g x ∂volume = (∫ x, Real.exp (-V x) ∂(volume.restrict U)) *
      ∫ x, c x * Real.exp (V x) * g x ∂((volume.restrict U).tilted fun x => -V x) := by
  have hzero : ∀ x ∉ U, c x * g x = 0 := fun x hx => by
    have hc : c x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hcU h))
    simp [hc]
  have hIa : ∀ x, (∫ y, Real.exp (-V y) ∂(volume.restrict U)) *
      (Real.exp (-V x) / ∫ y, Real.exp (-V y) ∂(volume.restrict U)) = Real.exp (-V x) := by
    intro x
    field_simp
  calc ∫ x, c x * g x ∂volume
      = ∫ x in U, c x * g x ∂volume := (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x, (∫ y, Real.exp (-V y) ∂(volume.restrict U)) *
          ((Real.exp (-V x) / ∫ y, Real.exp (-V y) ∂(volume.restrict U)) •
            (c x * Real.exp (V x) * g x)) ∂(volume.restrict U) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [smul_eq_mul]
        have he := exp_neg_mul_exp (V x)
        rw [← mul_assoc, hIa x]
        linear_combination (-(c x * g x)) * he
    _ = (∫ y, Real.exp (-V y) ∂(volume.restrict U)) *
          ∫ x, (Real.exp (-V x) / ∫ y, Real.exp (-V y) ∂(volume.restrict U)) •
            (c x * Real.exp (V x) * g x) ∂(volume.restrict U) := integral_const_mul _ _
    _ = _ := by rw [integral_tilted]

/-- For a test function `c` supported in `U`, the function `c exp V` lies in `L²` of the tilted
measure. Continuity of `V` on `U` gives this bound, and it is the only place where that continuity
is used. -/
theorem memLp_two_tilted_mul_exp {U : Set (EuclideanSpace ℝ (Fin n))}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) (hV : ContinuousOn V U)
    (hexp : Integrable (fun x => Real.exp (-V x)) (volume.restrict U))
    {c : EuclideanSpace ℝ (Fin n) → ℝ} (hc : Continuous c) (hcc : HasCompactSupport c)
    (hcU : tsupport c ⊆ U) :
    MemLp (fun x => c x * Real.exp (V x)) 2 ((volume.restrict U).tilted fun x => -V x) := by
  have hexpV : ContinuousOn (fun x => Real.exp (V x)) U :=
    Real.continuous_exp.comp_continuousOn hV
  have hcont : Continuous (fun x => c x * Real.exp (V x)) :=
    Riesz1.WeightedSobolev.continuous_cutoff_mul hU hc hcU hexpV
  have hcc2 : Continuous (fun x => c x * c x * Real.exp (V x)) :=
    Riesz1.WeightedSobolev.continuous_cutoff_mul hU (hc.mul hc)
      (tsupport_mul_subset_left.trans hcU) hexpV
  have hint : Integrable (fun x => c x * c x * Real.exp (V x)) volume :=
    hcc2.integrable_of_hasCompactSupport (hcc.mul_right.mul_right)
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable, integrable_tilted_iff hexp]
  refine (hint.restrict).congr (Eventually.of_forall fun x => ?_)
  have he := exp_neg_mul_exp (V x)
  simp only [smul_eq_mul]
  linear_combination (-(c x * c x * Real.exp (V x))) * he

/-- A function in `L²` of the tilted measure, multiplied by a test function `c` supported in `U`,
is integrable for the Lebesgue measure. -/
theorem integrable_mul_of_memLp_tilted {U : Set (EuclideanSpace ℝ (Fin n))}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) (hV : ContinuousOn V U)
    (hexp : Integrable (fun x => Real.exp (-V x)) (volume.restrict U))
    {c : EuclideanSpace ℝ (Fin n) → ℝ} (hc : Continuous c) (hcc : HasCompactSupport c)
    (hcU : tsupport c ⊆ U) {p : EuclideanSpace ℝ (Fin n) → ℝ}
    (hp : MemLp p 2 ((volume.restrict U).tilted fun x => -V x)) :
    Integrable (fun x => c x * p x) volume := by
  have h1 : Integrable (fun x => c x * Real.exp (V x) * p x)
      ((volume.restrict U).tilted fun x => -V x) :=
    (memLp_two_tilted_mul_exp hU hV hexp hc hcc hcU).integrable_mul hp
  rw [integrable_tilted_iff hexp] at h1
  have h2 : Integrable (fun x => c x * p x) (volume.restrict U) := by
    refine h1.congr (Eventually.of_forall fun x => ?_)
    have he := exp_neg_mul_exp (V x)
    simp only [smul_eq_mul]
    linear_combination (c x * p x) * he
  have hsupp : Function.support (fun x => c x * p x) ⊆ U := fun x hx =>
    hcU (subset_tsupport c (left_ne_zero_of_mul hx))
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 h2

/-- A continuous compactly supported cutoff inside `U` times a function continuous on `U` is
integrable for the Lebesgue measure. -/
theorem integrable_cutoff_mul_of_continuousOn {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {c : EuclideanSpace ℝ (Fin n) → ℝ} (hc : Continuous c)
    (hcc : HasCompactSupport c) (hcU : tsupport c ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContinuousOn f U) :
    Integrable (fun x => c x * f x) volume :=
  (Riesz1.WeightedSobolev.continuous_cutoff_mul hU hc hcU hf).integrable_of_hasCompactSupport
    hcc.mul_right

/-- A function in `L²` of the tilted measure is locally integrable on `U`. -/
theorem locallyIntegrableOn_of_memLp_tilted {U : Set (EuclideanSpace ℝ (Fin n))}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) (hV : ContinuousOn V U)
    (hexp : Integrable (fun x => Real.exp (-V x)) (volume.restrict U))
    {p : EuclideanSpace ℝ (Fin n) → ℝ}
    (hpm : AEStronglyMeasurable p ((volume.restrict U).tilted fun x => -V x))
    (hp : MemLp p 2 ((volume.restrict U).tilted fun x => -V x)) :
    LocallyIntegrableOn p U volume := by
  intro x hx
  obtain ⟨c, hcU, hcc, hcd, -, hcx⟩ := exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hx)
  have hct : IsOpen {y | (1 / 2 : ℝ) < c y} := isOpen_lt continuous_const hcd.continuous
  have hsub : {y | (1 / 2 : ℝ) < c y} ⊆ U := fun y hy => by
    have hy' : (1 / 2 : ℝ) < c y := hy
    exact hcU (subset_tsupport c (lt_trans (by norm_num) hy').ne')
  refine ⟨{y | (1 / 2 : ℝ) < c y},
    mem_nhdsWithin_of_mem_nhds (hct.mem_nhds (by show (1 / 2 : ℝ) < c x; rw [hcx]; norm_num)),
    ?_⟩
  have hcp : Integrable (fun y => c y * p y) volume :=
    integrable_mul_of_memLp_tilted hU hV hexp hcd.continuous hcc hcU hp
  have hac : (volume.restrict {y | (1 / 2 : ℝ) < c y}) ≪
      (volume.restrict U).tilted fun x => -V x :=
    (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hsub le_rfl)).trans
      (absolutelyContinuous_tilted hexp)
  refine Integrable.mono' (g := fun y => 2 * ‖c y * p y‖) (hcp.norm.const_mul 2).integrableOn
    (hpm.mono_ac hac) ?_
  refine (ae_restrict_mem hct.measurableSet).mono fun y hy => ?_
  have hy' : (1 / 2 : ℝ) < c y := hy
  rw [norm_mul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ c y)]
  nlinarith [norm_nonneg (p y)]

end Tilted

/-! ### Measurability and smoothness on `U` -/

section Smooth

/-- A function continuous on `U` is almost everywhere strongly measurable for the tilted measure. -/
theorem aestronglyMeasurable_tilted_of_continuousOn {U : Set (EuclideanSpace ℝ (Fin n))}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {f : EuclideanSpace ℝ (Fin n) → E'} (hf : ContinuousOn f U) :
    AEStronglyMeasurable f ((volume.restrict U).tilted fun x => -V x) :=
  (hf.aestronglyMeasurable hU.measurableSet).mono_ac (tilted_absolutelyContinuous _ _)

/-- A smooth function near the closure of `U` is smooth on `U`. -/
theorem contDiffOn_of_smoothNearClosure {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Riesz1.WeightedSobolev.SmoothNearClosure U f) : ContDiffOn ℝ ∞ f U := by
  obtain ⟨W, -, hUW, hfW⟩ := hf
  exact hfW.mono (subset_closure.trans hUW)

/-- The gradient of a smooth function near the closure of `U` is continuous on `U`. -/
theorem continuousOn_gradient_of_smoothNearClosure {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Riesz1.WeightedSobolev.SmoothNearClosure U f) : ContinuousOn (gradient f) U := by
  obtain ⟨W, hW, hUW, hfW⟩ := hf
  have h1 : ContinuousOn (fderiv ℝ f) W := hfW.continuousOn_fderiv_of_isOpen hW (by norm_num)
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp_continuousOn
    (h1.mono (subset_closure.trans hUW))

/-- The inner product of the gradient with a fixed vector is the directional derivative. -/
theorem inner_gradient_eq_fderiv' (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) : inner ℝ (gradient f x) v = fderiv ℝ f x v :=
  InnerProductSpace.toDual_symm_apply

/-- Integration by parts for a directional derivative against a compactly supported smooth
function, on an open set `U` containing its support. -/
theorem integral_mul_fderiv_eq_neg {U : Set (EuclideanSpace ℝ (Fin n))}
    {f ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ψ x * fderiv ℝ f x v ∂volume = -∫ x, f x * fderiv ℝ ψ x v ∂volume := by
  have h := Riesz1.WeightedSobolev.integral_weighted_fderiv_of_compact_test (μ := volume) hU hψ
    hψc hψU hf (w := fun _ => (1 : ℝ)) contDiffOn_const v
  simp only [mul_one] at h
  exact h

/-- Integration by parts for the gradient pairing with a fixed vector. -/
theorem integral_mul_inner_gradient_eq_neg {U : Set (EuclideanSpace ℝ (Fin n))}
    {f ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ψ x * inner ℝ (gradient f x) v ∂volume = -∫ x, f x * fderiv ℝ ψ x v ∂volume := by
  simp only [inner_gradient_eq_fderiv']
  exact integral_mul_fderiv_eq_neg hU hf hψ hψc hψU v

end Smooth

/-! ### Passing to the limit against test functions -/

section Limits

/-- A test integral passes to the limit along a sequence whose differences converge in the
tilted `L²` norm. -/
theorem tendsto_integral_mul_of_tilted {U : Set (EuclideanSpace ℝ (Fin n))}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) (hV : ContinuousOn V U)
    (hexp : Integrable (fun x => Real.exp (-V x)) (volume.restrict U))
    (hI : ∫ x, Real.exp (-V x) ∂(volume.restrict U) ≠ 0)
    {c : EuclideanSpace ℝ (Fin n) → ℝ} (hc : Continuous c) (hcc : HasCompactSupport c)
    (hcU : tsupport c ⊆ U) {p : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {p₀ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hint : ∀ k, Integrable (fun x => c x * p k x) volume)
    (hint₀ : Integrable (fun x => c x * p₀ x) volume)
    (hd : ∀ᶠ k in atTop,
      MemLp (fun x => p k x - p₀ x) 2 ((volume.restrict U).tilted fun x => -V x))
    (hdT : Tendsto (fun k => ∫ x, (p k x - p₀ x) ^ 2
      ∂((volume.restrict U).tilted fun x => -V x)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, c x * p k x ∂volume) atTop (𝓝 (∫ x, c x * p₀ x ∂volume)) := by
  have hθ := memLp_two_tilted_mul_exp hU hV hexp hc hcc hcU
  have hdiff : ∀ k, (∫ x, c x * p k x ∂volume) - ∫ x, c x * p₀ x ∂volume =
      (∫ x, Real.exp (-V x) ∂(volume.restrict U)) *
        ∫ x, c x * Real.exp (V x) * (p k x - p₀ x)
          ∂((volume.restrict U).tilted fun x => -V x) := by
    intro k
    rw [← integral_sub (hint k) hint₀]
    have hmul : ∀ x, c x * p k x - c x * p₀ x = c x * (p k x - p₀ x) :=
      fun x => (mul_sub _ _ _).symm
    simp_rw [hmul]
    exact integral_mul_eq_integral_tilted hI hcU (fun x => p k x - p₀ x)
  have hbound : ∀ᶠ k in atTop,
      |∫ x, c x * Real.exp (V x) * (p k x - p₀ x) ∂((volume.restrict U).tilted fun x => -V x)| ≤
        Real.sqrt (∫ x, (c x * Real.exp (V x)) ^ 2 ∂((volume.restrict U).tilted fun x => -V x)) *
          Real.sqrt (∫ x, (p k x - p₀ x) ^ 2 ∂((volume.restrict U).tilted fun x => -V x)) :=
    hd.mono fun k hk => Riesz1.WeightedSobolev.abs_integral_mul_le_sqrt hθ hk
  have hsq : Tendsto (fun k => Real.sqrt
      (∫ x, (p k x - p₀ x) ^ 2 ∂((volume.restrict U).tilted fun x => -V x))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hdT
    rw [Real.sqrt_zero] at h
    exact h
  have hsqrt : Tendsto (fun k =>
      Real.sqrt (∫ x, (c x * Real.exp (V x)) ^ 2 ∂((volume.restrict U).tilted fun x => -V x)) *
        Real.sqrt (∫ x, (p k x - p₀ x) ^ 2 ∂((volume.restrict U).tilted fun x => -V x)))
      atTop (𝓝 0) := by
    have h := hsq.const_mul
      (Real.sqrt (∫ x, (c x * Real.exp (V x)) ^ 2 ∂((volume.restrict U).tilted fun x => -V x)))
    rw [mul_zero] at h
    exact h
  have hT0 : Tendsto (fun k => ∫ x, c x * Real.exp (V x) * (p k x - p₀ x)
      ∂((volume.restrict U).tilted fun x => -V x)) atTop (𝓝 0) :=
    squeeze_zero_norm' (hbound.mono fun k hk => by rw [Real.norm_eq_abs]; exact hk) hsqrt
  have hlim : Tendsto (fun k => (∫ x, c x * p k x ∂volume) - ∫ x, c x * p₀ x ∂volume)
      atTop (𝓝 0) := by
    have h := hT0.const_mul (∫ x, Real.exp (-V x) ∂(volume.restrict U))
    rw [mul_zero] at h
    exact h.congr fun k => (hdiff k).symm
  exact tendsto_sub_nhds_zero_iff.1 hlim

end Limits

/-! ### The weak gradient identity against test functions, and the fundamental lemma -/

section Identification

/-- The weak gradient pairs with a test function as the classical derivative does. For every
smooth test function `ψ` supported in `U` and every vector `v`, the identity
`∫ ψ ⟪G, v⟫ = ∫ ψ ∂_v F` holds. -/
theorem integral_mul_inner_eq_of_test {U : Set (EuclideanSpace ℝ (Fin n))}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) (hV : ContinuousOn V U)
    (hexp : Integrable (fun x => Real.exp (-V x)) (volume.restrict U))
    (hI : ∫ x, Real.exp (-V x) ∂(volume.restrict U) ≠ 0)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hGL : MemLp G 2 ((volume.restrict U).tilted fun x => -V x))
    {φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hφS : ∀ k, Riesz1.WeightedSobolev.SmoothNearClosure U (φ k))
    (hT1 : Tendsto (fun k => ∫⁻ x, ‖φ k x - F x‖ₑ ^ 2
      ∂((volume.restrict U).tilted fun x => -V x)) atTop (𝓝 0))
    (hT2 : Tendsto (fun k => ∫⁻ x, ‖gradient (φ k) x - G x‖ₑ ^ 2
      ∂((volume.restrict U).tilted fun x => -V x)) atTop (𝓝 0))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ψ x * inner ℝ (G x) v ∂volume = ∫ x, ψ x * fderiv ℝ F x v ∂volume := by
  have hψc0 : Continuous ψ := hψ.continuous
  have hFc : ContinuousOn F U := hF.continuousOn
  have hχc : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hχcc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := hψc.fderiv_apply ℝ v
  have hχU : tsupport (fun x => fderiv ℝ ψ x v) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ v).trans hψU
  have hφc : ∀ k, ContinuousOn (φ k) U := fun k => (contDiffOn_of_smoothNearClosure (hφS k)).continuousOn
  have hgradc : ∀ k, ContinuousOn (gradient (φ k)) U :=
    fun k => continuousOn_gradient_of_smoothNearClosure (hφS k)
  have hpG : MemLp (fun x => inner ℝ (G x) v) 2 ((volume.restrict U).tilted fun x => -V x) :=
    memLp_inner_of_memLp hGL v
  have hint₀ : Integrable (fun x => ψ x * inner ℝ (G x) v) volume :=
    integrable_mul_of_memLp_tilted hU hV hexp hψc0 hψc hψU hpG
  have hgcont : ∀ k, ContinuousOn (fun x => inner ℝ (gradient (φ k) x) v) U := fun k =>
    (hgradc k).inner continuousOn_const
  have hint : ∀ k, Integrable (fun x => ψ x * inner ℝ (gradient (φ k) x) v) volume := fun k =>
    integrable_cutoff_mul_of_continuousOn hU hψc0 hψc hψU (hgcont k)
  have hgm : ∀ k, AEStronglyMeasurable (fun x => gradient (φ k) x - G x)
      ((volume.restrict U).tilted fun x => -V x) := fun k =>
    (aestronglyMeasurable_tilted_of_continuousOn hU (hgradc k)).sub hGL.aestronglyMeasurable
  obtain ⟨hdG, hdGT⟩ := eventually_memLp_and_tendsto_inner
    (a := fun k x => gradient (φ k) x - G x) hgm hT2 v
  have heq : ∀ k, (fun x => inner ℝ (gradient (φ k) x) v - inner ℝ (G x) v) =
      fun x => inner ℝ (gradient (φ k) x - G x) v := fun k => by
    funext x
    rw [inner_sub_left]
  have hd : ∀ᶠ k in atTop, MemLp (fun x => inner ℝ (gradient (φ k) x) v - inner ℝ (G x) v) 2
      ((volume.restrict U).tilted fun x => -V x) := by
    refine hdG.mono fun k hk => ?_
    rw [heq k]
    exact hk
  have hdT : Tendsto (fun k => ∫ x, (inner ℝ (gradient (φ k) x) v - inner ℝ (G x) v) ^ 2
      ∂((volume.restrict U).tilted fun x => -V x)) atTop (𝓝 0) := by
    refine hdGT.congr fun k => ?_
    simp only [inner_sub_left]
  have h2 := tendsto_integral_mul_of_tilted hU hV hexp hI hψc0 hψc hψU
    (p := fun k x => inner ℝ (gradient (φ k) x) v) (p₀ := fun x => inner ℝ (G x) v) hint hint₀
    hd hdT
  have hibp : ∀ k, ∫ x, ψ x * inner ℝ (gradient (φ k) x) v ∂volume =
      -∫ x, φ k x * fderiv ℝ ψ x v ∂volume := fun k =>
    integral_mul_inner_gradient_eq_neg hU (contDiffOn_of_smoothNearClosure (hφS k)) hψ hψc hψU v
  have h2' := h2.congr fun k => hibp k
  -- The approximating functions converge against `ψ`-tests via `fderiv ψ · v`.
  have hfm : ∀ k, AEStronglyMeasurable (fun x => φ k x - F x)
      ((volume.restrict U).tilted fun x => -V x) := fun k =>
    aestronglyMeasurable_tilted_of_continuousOn hU ((hφc k).sub hFc)
  have hφF : ∀ᶠ k in atTop, MemLp (fun x => φ k x - F x) 2
      ((volume.restrict U).tilted fun x => -V x) :=
    eventually_memLp_of_tendsto_lintegral hfm hT1
  have hφFT : Tendsto (fun k => ∫ x, (φ k x - F x) ^ 2
      ∂((volume.restrict U).tilted fun x => -V x)) atTop (𝓝 0) :=
    Riesz1.WeightedSobolev.tendsto_integral_sq_of_lintegral hfm hT1
  have h3 := tendsto_integral_mul_of_tilted hU hV hexp hI hχc hχcc hχU
    (p := φ) (p₀ := F) (fun k => integrable_cutoff_mul_of_continuousOn hU hχc hχcc hχU (hφc k))
    (integrable_cutoff_mul_of_continuousOn hU hχc hχcc hχU hFc) hφF hφFT
  have hcomm : ∀ k, ∫ x, φ k x * fderiv ℝ ψ x v ∂volume =
      ∫ x, fderiv ℝ ψ x v * φ k x ∂volume := fun k =>
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have h3' : Tendsto (fun k => -∫ x, φ k x * fderiv ℝ ψ x v ∂volume) atTop
      (𝓝 (-∫ x, fderiv ℝ ψ x v * F x ∂volume)) :=
    h3.neg.congr fun k => by rw [hcomm k]
  have hlim := tendsto_nhds_unique h2' h3'
  have hF' := integral_mul_fderiv_eq_neg hU hF hψ hψc hψU v
  have hcomm2 : ∫ x, F x * fderiv ℝ ψ x v ∂volume = ∫ x, fderiv ℝ ψ x v * F x ∂volume :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hF', hcomm2]
  exact hlim

/-- The weak gradient agrees with the classical gradient, paired with a fixed vector, almost
everywhere on `U`. -/
theorem ae_inner_eq_fderiv {U : Set (EuclideanSpace ℝ (Fin n))}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) (hV : ContinuousOn V U)
    (hexp : Integrable (fun x => Real.exp (-V x)) (volume.restrict U))
    (hI : ∫ x, Real.exp (-V x) ∂(volume.restrict U) ≠ 0)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hGL : MemLp G 2 ((volume.restrict U).tilted fun x => -V x))
    {φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hφS : ∀ k, Riesz1.WeightedSobolev.SmoothNearClosure U (φ k))
    (hT1 : Tendsto (fun k => ∫⁻ x, ‖φ k x - F x‖ₑ ^ 2
      ∂((volume.restrict U).tilted fun x => -V x)) atTop (𝓝 0))
    (hT2 : Tendsto (fun k => ∫⁻ x, ‖gradient (φ k) x - G x‖ₑ ^ 2
      ∂((volume.restrict U).tilted fun x => -V x)) atTop (𝓝 0))
    (v : EuclideanSpace ℝ (Fin n)) :
    ∀ᵐ x ∂volume, x ∈ U → inner ℝ (G x) v = fderiv ℝ F x v := by
  have hpG : MemLp (fun x => inner ℝ (G x) v) 2 ((volume.restrict U).tilted fun x => -V x) :=
    memLp_inner_of_memLp hGL v
  have hqc : ContinuousOn (fun x => fderiv ℝ F x v) U :=
    (hF.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const
  have hloc : LocallyIntegrableOn (fun x => inner ℝ (G x) v - fderiv ℝ F x v) U volume :=
    (locallyIntegrableOn_of_memLp_tilted hU hV hexp hpG.aestronglyMeasurable hpG).sub
      (hqc.locallyIntegrableOn hU.measurableSet)
  have hzero : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ U →
        ∫ x, g x • (inner ℝ (G x) v - fderiv ℝ F x v) ∂volume = 0 := by
    intro g hg hgc hgU
    have h1 := integrable_mul_of_memLp_tilted hU hV hexp hg.continuous hgc hgU hpG
    have h2 := integrable_cutoff_mul_of_continuousOn hU hg.continuous hgc hgU hqc
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub h1 h2,
      integral_mul_inner_eq_of_test hU hV hexp hI hF hGL hφS hT1 hT2 hg hgc hgU v, sub_self]
  have h0 := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hU hloc hzero
  filter_upwards [h0] with x hx hxU
  exact sub_eq_zero.1 (hx hxU)

end Identification

/-! ### The main result -/

/-- The weak gradient of a function `F` in the weighted Sobolev completion `IsWeightedH1 ν U F G`
equals the classical gradient of `F` almost everywhere, when `F` is smooth on the open set `U`,
the density of `ν` is `exp(-V)` on `U`, and `V` is continuous on `U`. -/
theorem ae_gradient_eq_of_isWeightedH1_of_continuousOn {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hexp : Integrable (fun x => Real.exp (-V x)) (volume.restrict U))
    (hV : ContinuousOn V U)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : Riesz1.WeightedSobolev.IsWeightedH1
      ((volume.restrict U).tilted (fun x => -V x)) U F G) :
    ∀ᵐ x ∂((volume.restrict U).tilted (fun x => -V x)), G x = gradient F x := by
  obtain ⟨-, hGL, φ, hφS, hT1, hT2⟩ := hG
  by_cases hI : ∫ x, Real.exp (-V x) ∂(volume.restrict U) = 0
  · have hν : (volume.restrict U).tilted (fun x => -V x) = 0 := by
      simp [Measure.tilted, hI]
    rw [hν, ae_zero]
    exact Filter.eventually_bot
  have hbasis : ∀ i : Fin n, ∀ᵐ x ∂volume, x ∈ U →
      inner ℝ (G x) (EuclideanSpace.basisFun (Fin n) ℝ i) =
        fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ i) := fun i =>
    ae_inner_eq_fderiv hU hV hexp hI hF hGL hφS hT1 hT2 _
  have hvol : ∀ᵐ x ∂volume, x ∈ U → G x = gradient F x := by
    filter_upwards [ae_all_iff.2 hbasis] with x hx hxU
    ext i
    have h : inner ℝ (G x) (EuclideanSpace.basisFun (Fin n) ℝ i) =
        inner ℝ (gradient F x) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
      rw [inner_gradient_eq_fderiv']
      exact hx i hxU
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right,
      EuclideanSpace.inner_single_right] at h
    simpa using h
  have hac := tilted_absolutelyContinuous (volume.restrict U) (fun x => -V x)
  have hν1 : ∀ᵐ x ∂((volume.restrict U).tilted fun x => -V x), x ∈ U → G x = gradient F x :=
    Filter.Eventually.filter_mono hac.ae_le (ae_restrict_of_ae hvol)
  have hν2 : ∀ᵐ x ∂((volume.restrict U).tilted fun x => -V x), x ∈ U :=
    Filter.Eventually.filter_mono hac.ae_le (ae_restrict_mem hU.measurableSet)
  filter_upwards [hν1, hν2] with x h1 h2
  exact h1 h2

end Riesz1.ConvexityHessian

end
