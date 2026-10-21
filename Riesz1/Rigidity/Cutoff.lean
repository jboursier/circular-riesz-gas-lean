/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The smooth forcing cutoff and its bounds

A cutoff is a function `θ : ℝ → ℝ` of class `C²` that
vanishes on `[0, 1]` and whose second derivative lies in `[0, 2]` on `[0, ∞)`. Here `θ` is
defined on `ℝ`, and only its values on `[0, ∞)` enter the bounds.

The first part shows that every cutoff satisfies the bounds `cutoff_bounds`, stated with `deriv`
and `deriv (deriv θ)`. The second part constructs the explicit cutoff `forcingCutoff`. It is
`C^∞`, vanishes on `(-∞, 1]`, has second derivative `forcingDensity` (the bump `h`),
and has second derivative `2` on `[2, ∞)`.
-/

public section

open Set
open scoped ContDiff Topology

namespace Riesz1

/-! ### Bounds for every cutoff -/

/-- The derivative of a cutoff vanishes on `[0, 1]`. The function `θ` is zero on `(0, 1)`, so
`θ'` is zero there. Continuity of `θ'` extends this to the closed interval. -/
theorem cutoff_deriv_eq_zero {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, θ t = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, deriv θ t = 0 := by
  have hcont : Continuous (deriv θ) := hθ.continuous_deriv (by norm_num)
  have hopen : ∀ t ∈ Ioo (0 : ℝ) 1, deriv θ t = 0 := by
    intro t ht
    have hev : θ =ᶠ[𝓝 t] fun _ => 0 :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
        hzero s (Ioo_subset_Icc_self hs)
    rw [hev.deriv_eq]
    simp
  have hclosed : Icc (0 : ℝ) 1 ⊆ {t | deriv θ t = 0} := by
    rw [← closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
    exact closure_minimal (fun t ht => hopen t ht) (isClosed_eq hcont continuous_const)
  exact fun t ht => hclosed ht

/-- The derivative `θ'` is nondecreasing on `[0, ∞)`, because `θ'' ≥ 0` there. -/
theorem cutoff_deriv_monotoneOn {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hθ'' : ∀ t, 0 ≤ t → 0 ≤ deriv (deriv θ) t ∧ deriv (deriv θ) t ≤ 2) :
    MonotoneOn (deriv θ) (Ici 0) := by
  have hdiff : Differentiable ℝ (deriv θ) := (hθ.deriv' (n := 1)).differentiable (by norm_num)
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
    hdiff.differentiableOn fun t ht => ?_
  rw [interior_Ici, mem_Ioi] at ht
  exact (hθ'' t ht.le).1

/-- The derivative `θ'` is nonnegative on `[0, ∞)`: it is nondecreasing there and vanishes at `0`. -/
theorem cutoff_deriv_nonneg {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, θ t = 0)
    (hθ'' : ∀ t, 0 ≤ t → 0 ≤ deriv (deriv θ) t ∧ deriv (deriv θ) t ≤ 2) :
    ∀ t, 0 ≤ t → 0 ≤ deriv θ t := by
  intro t ht
  have h := cutoff_deriv_monotoneOn hθ hθ'' self_mem_Ici (mem_Ici.2 ht) ht
  have h0 := cutoff_deriv_eq_zero hθ hzero 0 ⟨le_rfl, zero_le_one⟩
  linarith

/-- The cutoff `θ` is nondecreasing on `[0, ∞)`, because `θ' ≥ 0` there. -/
theorem cutoff_monotoneOn {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, θ t = 0)
    (hθ'' : ∀ t, 0 ≤ t → 0 ≤ deriv (deriv θ) t ∧ deriv (deriv θ) t ≤ 2) :
    MonotoneOn θ (Ici 0) := by
  have hdiff : Differentiable ℝ θ := hθ.differentiable (by norm_num)
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
    hdiff.differentiableOn fun t ht => ?_
  rw [interior_Ici, mem_Ioi] at ht
  exact cutoff_deriv_nonneg hθ hzero hθ'' t ht.le

/-- For `t ≥ 1` the derivative satisfies `θ'(t) ≤ 2 (t - 1)`. The function
`s ↦ θ'(s) - 2 (s - 1)` is nonincreasing on `[1, ∞)` and vanishes at `s = 1`. -/
theorem cutoff_deriv_le_of_one_le {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, θ t = 0)
    (hθ'' : ∀ t, 0 ≤ t → 0 ≤ deriv (deriv θ) t ∧ deriv (deriv θ) t ≤ 2) :
    ∀ t, 1 ≤ t → deriv θ t ≤ 2 * (t - 1) := by
  have hdiff : Differentiable ℝ (deriv θ) := (hθ.deriv' (n := 1)).differentiable (by norm_num)
  have hg : ∀ s : ℝ, HasDerivAt (fun s => deriv θ s - 2 * (s - 1)) (deriv (deriv θ) s - 2) s := by
    intro s
    have h2 : HasDerivAt (fun s : ℝ => 2 * (s - 1)) 2 s := by
      simpa using ((hasDerivAt_id s).sub_const 1).const_mul 2
    exact (hdiff s).hasDerivAt.sub h2
  have hdg : Differentiable ℝ (fun s => deriv θ s - 2 * (s - 1)) :=
    fun s => (hg s).differentiableAt
  have hanti : AntitoneOn (fun s => deriv θ s - 2 * (s - 1)) (Ici 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 1) hdg.continuous.continuousOn
      hdg.differentiableOn fun s hs => ?_
    rw [interior_Ici, mem_Ioi] at hs
    rw [(hg s).deriv]
    linarith [(hθ'' s (by linarith)).2]
  intro t ht
  have h1 := hanti self_mem_Ici (mem_Ici.2 ht) ht
  have h1' := cutoff_deriv_eq_zero hθ hzero 1 ⟨zero_le_one, le_rfl⟩
  dsimp only at h1
  linarith

/-- The derivative satisfies `0 ≤ θ'(t) ≤ 2 max (t - 1) 0` for `t ≥ 0`. -/
theorem cutoff_deriv_le {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, θ t = 0)
    (hθ'' : ∀ t, 0 ≤ t → 0 ≤ deriv (deriv θ) t ∧ deriv (deriv θ) t ≤ 2) :
    ∀ t, 0 ≤ t → deriv θ t ≤ 2 * max (t - 1) 0 := by
  intro t ht
  rcases le_total t 1 with h | h
  · have hmax : max (t - 1) 0 = 0 := max_eq_right (by linarith)
    rw [hmax, cutoff_deriv_eq_zero hθ hzero t ⟨ht, h⟩]
    norm_num
  · have hmax : max (t - 1) 0 = t - 1 := max_eq_left (by linarith)
    rw [hmax]
    exact cutoff_deriv_le_of_one_le hθ hzero hθ'' t h

/-- The cutoff satisfies `0 ≤ θ(t) ≤ max (t - 1) 0 ^ 2` for `t ≥ 0`. -/
theorem cutoff_le_sq {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, θ t = 0)
    (hθ'' : ∀ t, 0 ≤ t → 0 ≤ deriv (deriv θ) t ∧ deriv (deriv θ) t ≤ 2) :
    ∀ t, 0 ≤ t → θ t ≤ max (t - 1) 0 ^ 2 := by
  have hdiff : Differentiable ℝ θ := hθ.differentiable (by norm_num)
  have hk : ∀ s : ℝ, HasDerivAt (fun s => θ s - (s - 1) ^ 2) (deriv θ s - 2 * (s - 1)) s := by
    intro s
    have h2 : HasDerivAt (fun s : ℝ => (s - 1) ^ 2) (2 * (s - 1)) s := by
      have h := (hasDerivAt_pow 2 (s - 1)).comp s ((hasDerivAt_id s).sub_const 1)
      exact h.congr_deriv (by norm_num)
    exact (hdiff s).hasDerivAt.sub h2
  have hdk : Differentiable ℝ (fun s => θ s - (s - 1) ^ 2) :=
    fun s => (hk s).differentiableAt
  have hanti : AntitoneOn (fun s => θ s - (s - 1) ^ 2) (Ici 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 1) hdk.continuous.continuousOn
      hdk.differentiableOn fun s hs => ?_
    rw [interior_Ici, mem_Ioi] at hs
    rw [(hk s).deriv]
    linarith [cutoff_deriv_le_of_one_le hθ hzero hθ'' s hs.le]
  intro t ht
  rcases le_total t 1 with h | h
  · have hmax : max (t - 1) 0 = 0 := max_eq_right (by linarith)
    rw [hmax, hzero t ⟨ht, h⟩]
    norm_num
  · have hmax : max (t - 1) 0 = t - 1 := max_eq_left (by linarith)
    have h1 := hanti self_mem_Ici (mem_Ici.2 h) h
    dsimp only at h1
    rw [hzero 1 ⟨zero_le_one, le_rfl⟩] at h1
    rw [hmax]
    linarith

/-- The cutoff is nonnegative on `[0, ∞)`, because it is nondecreasing there and vanishes at `0`. -/
theorem cutoff_nonneg {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, θ t = 0)
    (hθ'' : ∀ t, 0 ≤ t → 0 ≤ deriv (deriv θ) t ∧ deriv (deriv θ) t ≤ 2) :
    ∀ t, 0 ≤ t → 0 ≤ θ t := by
  intro t ht
  have h := cutoff_monotoneOn hθ hzero hθ'' self_mem_Ici (mem_Ici.2 ht) ht
  have h0 := hzero 0 ⟨le_rfl, zero_le_one⟩
  linarith

/-- The bounds for every cutoff `θ`. -/
theorem cutoff_bounds {θ : ℝ → ℝ} (hθ : ContDiff ℝ 2 θ)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, θ t = 0)
    (hθ'' : ∀ t, 0 ≤ t → 0 ≤ deriv (deriv θ) t ∧ deriv (deriv θ) t ≤ 2) :
    MonotoneOn θ (Ici 0) ∧ MonotoneOn (deriv θ) (Ici 0) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, deriv θ t = 0) ∧
      (∀ t, 0 ≤ t → 0 ≤ deriv θ t ∧ deriv θ t ≤ 2 * max (t - 1) 0 ∧ 2 * max (t - 1) 0 ≤ 2 * t) ∧
      (∀ t, 0 ≤ t → 0 ≤ θ t ∧ θ t ≤ max (t - 1) 0 ^ 2 ∧ max (t - 1) 0 ^ 2 ≤ t ^ 2) ∧
      θ 2 ≤ 1 := by
  have hd := cutoff_deriv_le hθ hzero hθ''
  have hsq := cutoff_le_sq hθ hzero hθ''
  refine ⟨cutoff_monotoneOn hθ hzero hθ'', cutoff_deriv_monotoneOn hθ hθ'',
    cutoff_deriv_eq_zero hθ hzero, fun t ht => ?_, fun t ht => ?_, ?_⟩
  · have hm : max (t - 1) 0 ≤ t := max_le (by linarith) ht
    exact ⟨cutoff_deriv_nonneg hθ hzero hθ'' t ht, hd t ht, by linarith⟩
  · have hm : max (t - 1) 0 ≤ t := max_le (by linarith) ht
    have hm0 : 0 ≤ max (t - 1) 0 := le_max_right _ _
    exact ⟨cutoff_nonneg hθ hzero hθ'' t ht, hsq t ht, pow_le_pow_left₀ hm0 hm 2⟩
  · have h2 := hsq 2 (by norm_num)
    have hm2 : max ((2 : ℝ) - 1) 0 = 1 := by norm_num
    rw [hm2] at h2
    linarith

/-! ### The explicit cutoff -/

/-- The density `h`, written with Mathlib's `Real.smoothTransition`.
Lemma `forcingDensity_eq` gives the form `2 a(u - 1) / (a(u - 1) + a(2 - u))`. -/
noncomputable def forcingDensity (u : ℝ) : ℝ :=
  2 * Real.smoothTransition (u - 1)

/-- The explicit cutoff `θ(t) = ∫_0^t (t - u) h(u) du`. -/
noncomputable def forcingCutoff (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, (t - u) * forcingDensity u

/-- The density in explicit form, with `a = expNegInvGlue`. -/
theorem forcingDensity_eq (u : ℝ) :
    forcingDensity u =
      2 * expNegInvGlue (u - 1) / (expNegInvGlue (u - 1) + expNegInvGlue (2 - u)) := by
  unfold forcingDensity Real.smoothTransition
  rw [show (1 : ℝ) - (u - 1) = 2 - u by ring]
  ring

/-- On `(0, ∞)` the function `a = expNegInvGlue` equals `exp (-1 / t)`. -/
theorem expNegInvGlue_eq_exp {t : ℝ} (ht : 0 < t) : expNegInvGlue t = Real.exp (-1 / t) := by
  simp only [expNegInvGlue, not_le.2 ht, ↓reduceIte]
  congr 1
  ring

theorem forcingDensity_nonneg (u : ℝ) : 0 ≤ forcingDensity u :=
  mul_nonneg zero_le_two (Real.smoothTransition.nonneg _)

theorem forcingDensity_le_two (u : ℝ) : forcingDensity u ≤ 2 := by
  have h := Real.smoothTransition.le_one (u - 1)
  unfold forcingDensity
  linarith

theorem forcingDensity_eq_two {u : ℝ} (hu : 2 ≤ u) : forcingDensity u = 2 := by
  unfold forcingDensity
  rw [Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ u - 1)]
  norm_num

theorem forcingDensity_eq_zero {u : ℝ} (hu : u ≤ 1) : forcingDensity u = 0 := by
  unfold forcingDensity
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : u - 1 ≤ 0)]
  norm_num

theorem forcingDensity_contDiff : ContDiff ℝ ∞ forcingDensity := by
  unfold forcingDensity
  fun_prop

theorem forcingDensity_continuous : Continuous forcingDensity :=
  forcingDensity_contDiff.continuous

/-- An integral from `0` to `t ≤ 1` of a function vanishing on `(-∞, 1]` is zero. -/
theorem intervalIntegral_eq_zero_of_le_one {g : ℝ → ℝ} (hg : ∀ u ≤ 1, g u = 0) {t : ℝ}
    (ht : t ≤ 1) : ∫ u in (0 : ℝ)..t, g u = 0 := by
  have hEq : EqOn g (fun _ => 0) (uIcc 0 t) := by
    intro u hu
    have hu1 : u ≤ 1 := by
      rcases Set.mem_uIcc.1 hu with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
    exact hg u hu1
  rw [intervalIntegral.integral_congr hEq]
  simp

/-- Expanding `(t - u) h(u)` gives `θ(t) = t H(t) - K(t)`, where `H(t) = ∫_0^t h` and
`K(t) = ∫_0^t u h(u) du`. -/
theorem forcingCutoff_eq (t : ℝ) :
    forcingCutoff t =
      t * (∫ u in (0 : ℝ)..t, forcingDensity u) - ∫ u in (0 : ℝ)..t, u * forcingDensity u := by
  unfold forcingCutoff
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
  · congr 1
    funext u
    ring
  · exact (continuous_const.mul forcingDensity_continuous).intervalIntegrable _ _
  · exact (continuous_id.mul forcingDensity_continuous).intervalIntegrable _ _

/-- The integral `H(t) = ∫_0^t h` has derivative `h(t)`. -/
theorem forcingDensity_integral_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => ∫ u in (0 : ℝ)..s, forcingDensity u) (forcingDensity t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (forcingDensity_continuous.intervalIntegrable _ _)
    (forcingDensity_continuous.stronglyMeasurableAtFilter _ _)
    forcingDensity_continuous.continuousAt

/-- The integral `K(t) = ∫_0^t u h(u) du` has derivative `t h(t)`. -/
theorem forcingMoment_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => ∫ u in (0 : ℝ)..s, u * forcingDensity u) (t * forcingDensity t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_id.mul forcingDensity_continuous).intervalIntegrable _ _)
    ((continuous_id.mul forcingDensity_continuous).stronglyMeasurableAtFilter _ _)
    (continuous_id.mul forcingDensity_continuous).continuousAt

/-- The first derivative of `forcingCutoff` is `H`. -/
theorem forcingCutoff_hasDerivAt (t : ℝ) :
    HasDerivAt forcingCutoff (∫ u in (0 : ℝ)..t, forcingDensity u) t := by
  have hfun : forcingCutoff = fun s =>
      s * (∫ u in (0 : ℝ)..s, forcingDensity u) - ∫ u in (0 : ℝ)..s, u * forcingDensity u :=
    funext forcingCutoff_eq
  have h := ((hasDerivAt_id' t).mul (forcingDensity_integral_hasDerivAt t)).sub
    (forcingMoment_hasDerivAt t)
  rw [hfun]
  exact h.congr_deriv (by ring)

theorem forcingCutoff_deriv : deriv forcingCutoff = fun t => ∫ u in (0 : ℝ)..t, forcingDensity u :=
  funext fun t => (forcingCutoff_hasDerivAt t).deriv

theorem forcingDensity_integral_deriv :
    deriv (fun t => ∫ u in (0 : ℝ)..t, forcingDensity u) = forcingDensity :=
  funext fun t => (forcingDensity_integral_hasDerivAt t).deriv

/-- The second derivative of `forcingCutoff` is the density `forcingDensity`. -/
theorem forcingCutoff_deriv_deriv : deriv (deriv forcingCutoff) = forcingDensity := by
  rw [forcingCutoff_deriv, forcingDensity_integral_deriv]

/-- The explicit cutoff is `C^∞` on `ℝ`. -/
theorem forcingCutoff_contDiff : ContDiff ℝ ∞ forcingCutoff := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (forcingCutoff_hasDerivAt t).differentiableAt, ?_⟩
  rw [forcingCutoff_deriv, contDiff_infty_iff_deriv, forcingDensity_integral_deriv]
  exact ⟨fun t => (forcingDensity_integral_hasDerivAt t).differentiableAt, forcingDensity_contDiff⟩

/-- The explicit cutoff is `C²`, the regularity required by `cutoff_bounds`. -/
theorem forcingCutoff_contDiff_two : ContDiff ℝ 2 forcingCutoff :=
  forcingCutoff_contDiff.of_le (by norm_num)

/-- The explicit cutoff vanishes on `(-∞, 1]`, in particular on `[0, 1]`. -/
theorem forcingCutoff_eq_zero {t : ℝ} (ht : t ≤ 1) : forcingCutoff t = 0 := by
  have h1 : ∫ u in (0 : ℝ)..t, forcingDensity u = 0 :=
    intervalIntegral_eq_zero_of_le_one (fun u hu => forcingDensity_eq_zero hu) ht
  have h2 : ∫ u in (0 : ℝ)..t, u * forcingDensity u = 0 :=
    intervalIntegral_eq_zero_of_le_one (fun u hu => by simp [forcingDensity_eq_zero hu]) ht
  rw [forcingCutoff_eq, h1, h2, mul_zero, sub_zero]

/-- The explicit cutoff has second derivative in `[0, 2]` on `[0, ∞)`. -/
theorem forcingCutoff_deriv_deriv_bounds :
    ∀ t, 0 ≤ t → 0 ≤ deriv (deriv forcingCutoff) t ∧ deriv (deriv forcingCutoff) t ≤ 2 := by
  intro t _
  rw [forcingCutoff_deriv_deriv]
  exact ⟨forcingDensity_nonneg t, forcingDensity_le_two t⟩

/-- The explicit cutoff has second derivative equal to `2` on `[2, ∞)`. -/
theorem forcingCutoff_deriv_deriv_of_two_le {t : ℝ} (ht : 2 ≤ t) :
    deriv (deriv forcingCutoff) t = 2 := by
  rw [forcingCutoff_deriv_deriv, forcingDensity_eq_two ht]

/-- The explicit cutoff satisfies `θ(2) ≤ 1`, from the bounds `cutoff_bounds`. -/
theorem forcingCutoff_two_le_one : forcingCutoff 2 ≤ 1 :=
  (cutoff_bounds forcingCutoff_contDiff_two (fun _ ht => forcingCutoff_eq_zero ht.2)
    forcingCutoff_deriv_deriv_bounds).2.2.2.2.2

end Riesz1
