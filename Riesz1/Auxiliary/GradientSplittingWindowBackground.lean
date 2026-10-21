/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowPVSecond
public import Riesz1.Auxiliary.GradientSplittingWindowParam
public import Riesz1.Auxiliary.GradientSplittingWindowSupport
public import Riesz1.ToMathlib.CircleBasics

/-!
# The background integral in the `v`-frame

Let `g = hurwitzKernel s`, `G = deriv g`, and fix a lift `x`. The coefficient
`D(v) = ℓ(ψ((x+v)/ℓ) - ψ(x/ℓ))` (`gradD`) satisfies `Z(x,x+v) v = D(v)`, so
every integrand of the background integral and of the two principal values of `V` is a multiple of
`G` or `G'`, with a coefficient built from `D`, `Z(x,x+·)` and `ψ'`. This file collects these
identities, the vanishing of the coefficients near integer endpoints, and the integrability of
`D G` on the window.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The coefficient `D(v) = ℓ(ψ((x+v)/ℓ) - ψ(x/ℓ))` of the background integrand in the `v`-frame. -/
def gradD (ψ : ℝ → ℝ) (ℓ x v : ℝ) : ℝ := ℓ * (ψ ((x + v) / ℓ) - ψ (x / ℓ))

/-- `Z(x, x+v) v = D(v)`. -/
lemma gradZ_mul_eq_gradD {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x v : ℝ) :
    gradZ ψ ℓ x (x + v) * v = gradD ψ ℓ x v := by
  have h := gradZ_mul_sub hψ hℓ x (x + v)
  rw [add_sub_cancel_left] at h
  exact h

/-- `D` has derivative `ψ'((x+v)/ℓ)` (the derivative of the background coefficient). -/
lemma gradD_hasDerivAt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (_hℓ : ℓ ≠ 0) (x v : ℝ) :
    HasDerivAt (gradD ψ ℓ x) (deriv ψ ((x + v) / ℓ)) v := by
  have hlin : HasDerivAt (fun v : ℝ => (x + v) / ℓ) (1 / ℓ) v := by
    simpa using ((hasDerivAt_id v).const_add x).div_const ℓ
  have hψd : HasDerivAt ψ (deriv ψ ((x + v) / ℓ)) ((x + v) / ℓ) :=
    ((hψ.differentiable (by simp)) _).hasDerivAt
  have h := (hψd.comp v hlin).const_mul ℓ |>.sub_const (ℓ * ψ (x / ℓ))
  have e : ℓ * (deriv ψ ((x + v) / ℓ) * (1 / ℓ)) = deriv ψ ((x + v) / ℓ) := by
    field_simp
  unfold gradD
  rw [← e]
  simpa [Function.comp_def, mul_sub] using h

/-- `D` is one-periodic. -/
lemma gradD_periodic {ψ : ℝ → ℝ} {ℓ : ℝ} (hp : Function.Periodic ψ (1 / ℓ)) (x : ℝ) :
    Function.Periodic (gradD ψ ℓ x) 1 := by
  intro v
  unfold gradD
  have h : (x + (v + 1)) / ℓ = (x + v) / ℓ + 1 / ℓ := by ring
  rw [h, hp]

/-- The pointwise identity behind `Z_x h = (Z - ψ'(x/ℓ)) G`: `Z_x(x, x+v) h(v)` is `(Z - q) G(v)`. -/
lemma gradZx_mul_kernelH_shift (ψ : ℝ → ℝ) (ℓ : ℝ) (s x v : ℝ) :
    gradZx ψ ℓ x (x + v) * gradKernelH s v
      = (gradZ ψ ℓ x (x + v) - deriv ψ (x / ℓ)) * deriv (hurwitzKernel s) v := by
  have h := gradZx_mul_kernelH ψ ℓ s x (x + v)
  rwa [add_sub_cancel_left] at h

/-- The pointwise identity behind `Z(x,x+v) h(v) = D(v) G(v)`. -/
lemma gradZ_mul_kernelH_shift {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (s x v : ℝ) :
    gradZ ψ ℓ x (x + v) * gradKernelH s v = gradD ψ ℓ x v * deriv (hurwitzKernel s) v := by
  have h := gradZ_mul_kernelH hψ hℓ s x (x + v)
  rw [add_sub_cancel_left] at h
  rw [h]
  rfl

/-- `iteratedDeriv 2 g = deriv (deriv g)`. -/
lemma iteratedDeriv_two_hurwitzKernel_eq (s : ℝ) :
    iteratedDeriv 2 (hurwitzKernel s) = deriv (deriv (hurwitzKernel s)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- The derivative identity off the integers: `Z(x,x+v) h'(v) = Z(x,x+v) G(v) + D(v) G'(v)`. -/
lemma gradZ_mul_deriv_kernelH {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x v : ℝ) (hv : (v : UnitAddCircle) ≠ 0) :
    gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v
      = gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v
        + gradD ψ ℓ x v * deriv (deriv (hurwitzKernel s)) v := by
  rw [deriv_gradKernelH_eq hs0 hs1 hv, iteratedDeriv_two_hurwitzKernel_eq]
  have h := gradZ_mul_eq_gradD hψ hℓ x v
  calc gradZ ψ ℓ x (x + v) * (deriv (hurwitzKernel s) v + v * deriv (deriv (hurwitzKernel s)) v)
      = gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v
        + (gradZ ψ ℓ x (x + v) * v) * deriv (deriv (hurwitzKernel s)) v := by ring
    _ = _ := by rw [h]

/-- The far lemma gives vanishing of `ψ(x/ℓ)` and `ψ'(x/ℓ)` when the lift is far from the integers,
and then `D` vanishes near every point at distance `t` from the integers after shifting by `x`. -/
lemma gradD_eventually_zero {ψ : ℝ → ℝ} {ℓ t : ℝ} (_hℓ : ℓ ≠ 0) (ht : 0 < t)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) {x v0 : ℝ}
    (hx : ∀ m : ℤ, t ≤ |x - m|) (hc : ∀ m : ℤ, t ≤ |(x + v0) - m|) :
    ∀ᶠ v in 𝓝 v0, gradD ψ ℓ x v = 0 := by
  have hψx : ψ (x / ℓ) = 0 :=
    (eventually_psi_zero_near ht hsupp hx).self_of_nhds
  have hcont : Tendsto (fun v : ℝ => x + v) (𝓝 v0) (𝓝 (x + v0)) :=
    tendsto_const_nhds.add tendsto_id
  have hpsi : ∀ᶠ v in 𝓝 v0, ψ ((x + v) / ℓ) = 0 :=
    hcont.eventually (eventually_psi_zero_near ht hsupp hc |> fun h => by
      filter_upwards [h] with y hy
      exact hy)
  filter_upwards [hpsi] with v hv
  unfold gradD
  rw [hv, hψx]
  ring

/-- A Lipschitz bound for `D` on `|w| ≤ 1/2`, uniform in the lift `x`. -/
lemma exists_gradD_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w : ℝ, |w| ≤ 1 / 2 → |gradD ψ ℓ x w| ≤ L * |w| := by
  set c := x / ℓ with hc
  have hcpt : IsCompact (Icc (c - 1 / (2 * ℓ)) (c + 1 / (2 * ℓ))) := isCompact_Icc
  obtain ⟨L, hL⟩ := hcpt.exists_bound_of_continuousOn
    (hψ.continuous_deriv le_rfl).continuousOn
  refine ⟨max L 0, le_max_right _ _, fun w hw => ?_⟩
  have hmem : (x + w) / ℓ ∈ Icc (c - 1 / (2 * ℓ)) (c + 1 / (2 * ℓ)) := by
    have h1 : |(x + w) / ℓ - c| ≤ 1 / (2 * ℓ) := by
      rw [show (x + w) / ℓ - c = w / ℓ by rw [hc]; ring, abs_div, abs_of_pos hℓ]
      exact div_le_div_of_nonneg_right hw hℓ.le |>.trans_eq (by ring)
    rw [abs_le] at h1
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hcmem : c ∈ Icc (c - 1 / (2 * ℓ)) (c + 1 / (2 * ℓ)) := by
    constructor <;> nlinarith [one_div_pos.2 (mul_pos two_pos hℓ)]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := ψ)
    (s := Icc (c - 1 / (2 * ℓ)) (c + 1 / (2 * ℓ))) (C := max L 0) (x := c) (y := (x + w) / ℓ)
    (fun z _ => (hψ.differentiable (by norm_num)) z)
    (fun z hz => (hL z hz).trans (le_max_left _ _)) (convex_Icc _ _) hcmem hmem
  rw [Real.norm_eq_abs, Real.norm_eq_abs, show (x + w) / ℓ - c = w / ℓ by rw [hc]; ring,
    abs_div, abs_of_pos hℓ] at h
  unfold gradD
  rw [← hc, abs_mul, abs_of_pos hℓ]
  calc ℓ * |ψ ((x + w) / ℓ) - ψ c| ≤ ℓ * (max L 0 * (|w| / ℓ)) :=
        mul_le_mul_of_nonneg_left h hℓ.le
    _ = max L 0 * |w| := by field_simp

/-- The `D`-bound at every point, by periodicity: `|D(v)| ≤ L · dist(v, ℤ)`. -/
lemma gradD_le_dist {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) (x : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v : ℝ, |gradD ψ ℓ x v| ≤ L * ‖(v : UnitAddCircle)‖ := by
  obtain ⟨L, hL0, hL⟩ := exists_gradD_le hψ hℓ x
  refine ⟨L, hL0, fun v => ?_⟩
  set r : ℤ := round v with hr
  have hper : gradD ψ ℓ x (v - r) = gradD ψ ℓ x v := by
    have := (gradD_periodic hp x).int_mul (-r) v
    rw [show v + ((-r : ℤ) : ℝ) * 1 = v - r by push_cast; ring] at this
    exact this
  rw [UnitAddCircle.norm_eq, ← hr, ← hper]
  exact hL (v - r) (by simpa [abs_sub_comm] using abs_sub_round v)

/-- The background integrand `D(v) G(v)` is interval integrable on every interval. -/
lemma intervalIntegrable_gradD_mul_deriv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x a b : ℝ) :
    IntervalIntegrable (fun v => gradD ψ ℓ x v * deriv (hurwitzKernel s) v) volume a b := by
  obtain ⟨L, hL0, hL⟩ := gradD_le_dist hψ hℓ hp x
  obtain ⟨C, hC, hGb⟩ := deriv_hurwitzKernel_bound s hs0 hs1
  have hgD : Continuous (gradD ψ ℓ x) := by
    unfold gradD
    exact continuous_const.mul ((hψ.continuous.comp (by fun_prop)).sub continuous_const)
  have hGc : ContinuousOn (deriv (hurwitzKernel s)) (Ioo 0 1) := fun v hv =>
    (contDiffAt_deriv_hurwitzKernel hs0 hs1 (coe_ne_zero_of_mem_Ioo01 hv.1 hv.2)).continuousAt
      |>.continuousWithinAt
  have hmaj := (integrableOn_rpow_majorant hs1).const_mul (L * C)
  have h01 : IntervalIntegrable (fun v => gradD ψ ℓ x v * deriv (hurwitzKernel s) v) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    refine Integrable.mono' hmaj ?_ ?_
    · exact ((hgD.continuousOn.mul hGc)).aestronglyMeasurable measurableSet_Ioo
    · refine (ae_restrict_mem measurableSet_Ioo).mono fun v hv => ?_
      have hne : (v : UnitAddCircle) ≠ 0 := coe_ne_zero_of_mem_Ioo01 hv.1 hv.2
      have hd : 0 < ‖(v : UnitAddCircle)‖ := norm_pos_iff.2 hne
      have h1 := hL v
      have h2 := hGb v hne
      rw [dist_zero_right] at h2
      rw [Real.norm_eq_abs, abs_mul]
      have hdist := dist_rpow_le_majorant (s := s) hv.1 hv.2
      rw [dist_zero_right] at hdist
      have hrp : ‖(v : UnitAddCircle)‖ ^ (-s - 1) = ‖(v : UnitAddCircle)‖ ^ (-s) / ‖(v : UnitAddCircle)‖ := by
        rw [Real.rpow_sub_one hd.ne']
      calc |gradD ψ ℓ x v| * |deriv (hurwitzKernel s) v|
          ≤ (L * ‖(v : UnitAddCircle)‖) * (C * ‖(v : UnitAddCircle)‖ ^ (-s - 1)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (L * C) * ‖(v : UnitAddCircle)‖ ^ (-s) := by
            rw [hrp]; field_simp
        _ ≤ (L * C) * (v ^ (-s) + (1 - v) ^ (-s)) :=
            mul_le_mul_of_nonneg_left (by simpa [dist_zero_right] using hdist) (by positivity)
  have hper : Function.Periodic (fun v => gradD ψ ℓ x v * deriv (hurwitzKernel s) v) 1 := by
    intro v
    simp only
    rw [gradD_periodic hp x v, deriv_hurwitzKernel_add_one' s v]
  exact hper.intervalIntegrable (t := 0) one_ne_zero (by rw [zero_add]; exact h01) a b

/-- Dominated convergence for the truncated integrals of an interval integrable function. -/
lemma tendsto_allowed_integral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) :
    Tendsto (fun δ : ℝ => ∫ v in a..b, (gradAllowed δ).indicator f v) (𝓝[>] 0)
      (𝓝 (∫ v in a..b, f v)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun v => |f v|)
    ?_ ?_ hf.abs ?_
  · refine Eventually.of_forall fun δ => ?_
    rw [uIoc_of_le hab]
    exact (hf.1.aestronglyMeasurable).indicator (gradAllowed_isClosed δ).measurableSet
  · refine Eventually.of_forall fun δ => ae_of_all volume fun v => fun _ => ?_
    exact (norm_indicator_le_norm_self _ _).trans (le_of_eq (Real.norm_eq_abs _))
  · have hnull : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ Set.range (Int.cast : ℤ → ℝ) :=
      (Set.countable_range _).ae_notMem volume
    filter_upwards [hnull] with v hv _
    have hv' : ∀ m : ℤ, v ≠ m := fun m h => hv ⟨m, h.symm⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_gradAllowed hv'] with δ hδ
    exact (indicator_of_mem hδ f).symm

lemma contDiff_gradD {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (ℓ x : ℝ) :
    ContDiff ℝ ∞ (gradD ψ ℓ x) := by
  unfold gradD
  exact contDiff_const.mul (((hψ.comp ((contDiff_const.add contDiff_id).div_const ℓ))).sub contDiff_const)

/-- `D'(v) = ψ'((x+v)/ℓ)`, the coefficient of the closed form. -/
lemma deriv_gradD_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x v : ℝ) :
    deriv (gradD ψ ℓ x) v = deriv ψ ((x + v) / ℓ) :=
  (gradD_hasDerivAt hψ hℓ x v).deriv

/-- The background integral in the `v`-frame, with the principal value formula at the endpoints:
`∫_a^b D G = D(b) g(b) - D(a) g(a) - ∫_a^b ψ'((x+v)/ℓ) g(v) dv`, when `D` vanishes near an integer
endpoint. -/
lemma integral_gradD_mul_eq_formula {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) {a b : ℝ}
    (hab : a < b) (ha : (∃ m : ℤ, a = m) → ∀ᶠ v in 𝓝 a, gradD ψ ℓ x v = 0)
    (hb : (∃ m : ℤ, b = m) → ∀ᶠ v in 𝓝 b, gradD ψ ℓ x v = 0) :
    ∫ v in a..b, gradD ψ ℓ x v * deriv (hurwitzKernel s) v
      = gradD ψ ℓ x b * hurwitzKernel s b - gradD ψ ℓ x a * hurwitzKernel s a
        - ∫ v in a..b, deriv ψ ((x + v) / ℓ) * hurwitzKernel s v := by
  have hG := tendsto_allowed_integral hab.le
    (intervalIntegrable_gradD_mul_deriv (hψ.of_le (by simp)) hℓ hp hs0 hs1 x a b)
  have hF := tendsto_truncated_by_parts_gen hs0 hs1 (Φ := gradD ψ ℓ x)
    ((contDiff_gradD hψ ℓ x).of_le (by simp)) hab ha hb
  have hder : ∫ v in a..b, deriv (gradD ψ ℓ x) v * hurwitzKernel s v
      = ∫ v in a..b, deriv ψ ((x + v) / ℓ) * hurwitzKernel s v := by
    apply intervalIntegral.integral_congr
    intro v _
    simp only
    rw [deriv_gradD_eq hψ hℓ.ne' x v]
  rw [← hder]
  exact tendsto_nhds_unique hG hF

/-- `ψ'` vanishes on `[t, 1 - t]` (`0 < t ≤ 1/2`) when `ψ` vanishes away from the integers. -/
lemma deriv_psi_zero_of_mem_Icc {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ t : ℝ} (hℓ : ℓ ≠ 0)
    (ht : 0 < t) (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) {z : ℝ}
    (hz : z ∈ Icc t (1 - t)) : deriv ψ (z / ℓ) = 0 := by
  have hfar : ∀ m : ℤ, t ≤ |z - m| := by
    intro m
    rcases le_or_gt m 0 with h | h
    · have hm : (m : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith [hz.1])]
      linarith [hz.1]
    · have hm : (1 : ℝ) ≤ m := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith [hz.2])]
      linarith [hz.2]
  exact deriv_psi_zero_of_eventually hℓ (eventually_psi_zero_near ht hsupp hfar)
    ((hψ.differentiable (by simp)) _)

/-- The period trick: over the partial window `[-t - x, t - x]` the coefficient `ψ'((x+v)/ℓ) g(v)`
integrates to the fixed-period integral over `[-1/2, 1/2]`. -/
lemma integral_deriv_psi_mul_eq_period {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {t : ℝ} (ht : 0 < t) (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (ht2 : t ≤ 1 / 2) (x : ℝ) :
    ∫ v in (-t - x)..(t - x), deriv ψ ((x + v) / ℓ) * hurwitzKernel s v
      = ∫ v in (-1 / 2 : ℝ)..(1 / 2), deriv ψ ((x + v) / ℓ) * hurwitzKernel s v := by
  set f : ℝ → ℝ := fun v => deriv ψ ((x + v) / ℓ) * hurwitzKernel s v with hf
  have hper : Function.Periodic f 1 := by
    intro v
    simp only [hf]
    have hd := deriv_periodic_of hp
    rw [show (x + (v + 1)) / ℓ = (x + v) / ℓ + 1 / ℓ by ring, hd ((x + v) / ℓ),
      hurwitzKernel_periodic s v]
  have hint : ∀ c d : ℝ, IntervalIntegrable f volume c d := fun c d =>
    (hurwitzKernel_intervalIntegrable_all hs0 hs1 c d).continuousOn_mul
      (((hψ.continuous_deriv (by simp)).comp (by fun_prop : Continuous fun v : ℝ => (x + v) / ℓ))
        |>.continuousOn)
  have hshift := hper.intervalIntegral_add_eq (-t - x) (-1 / 2)
  have ha1 : (-t - x) + 1 = (t - x) + (1 - 2 * t) := by ring
  have hsplit : ∫ v in (-t - x)..((-t - x) + 1), f v
      = (∫ v in (-t - x)..(t - x), f v) + ∫ v in (t - x)..((-t - x) + 1), f v :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have hzero : ∫ v in (t - x)..((-t - x) + 1), f v = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun v hv => ?_),
      intervalIntegral.integral_zero]
    rw [uIcc_of_le (by linarith)] at hv
    have hz : x + v ∈ Icc t (1 - t) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    simp only [hf]
    rw [deriv_psi_zero_of_mem_Icc hψ hℓ.ne' ht hsupp hz, zero_mul]
  have h1 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [h1] at hshift
  rw [hsplit, hzero, add_zero] at hshift
  exact hshift

/-- The background integral of the window in the `v`-frame: `∫_B Z(x,y)h(y-x) dy = ∫ D(v) G(v) dv`. -/
lemma gradBackground_eq_vframe (s : ℝ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (N : ℕ+) {ℓ γ : ℝ}
    (hℓ : ℓ ≠ 0) (x : ℝ) :
    gradBackground s ψ N ℓ γ x = ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
      gradD ψ ℓ x v * deriv (hurwitzKernel s) v := by
  unfold gradBackground
  have h := intervalIntegral.integral_comp_add_right
    (fun y : ℝ => gradZ ψ ℓ x y * gradKernelH s (y - x)) x
    (a := gradBLo N ℓ γ x - x) (b := gradBHi N ℓ γ x - x)
  simp only [sub_add_cancel] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro v _
  simp only
  rw [add_sub_cancel_right, add_comm v x, gradZ_mul_kernelH_shift hψ hℓ s x v]

/-- The change of variables `y = x + v` turns the `y`-frame truncation of the principal value
into the `v`-frame truncation. -/
lemma gradPV_integral_eq_vframe (N : ℕ+) (ℓ γ x : ℝ) (f : ℝ → ℝ) (δ : ℝ) :
    ∫ y in gradBLo N ℓ γ x..gradBHi N ℓ γ x,
      Set.indicator {y : ℝ | ∀ m : ℤ, δ ≤ |y - x - m|} f y
        = ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
          (gradAllowed δ).indicator (fun v => f (x + v)) v := by
  have h := intervalIntegral.integral_comp_add_right
    (fun y : ℝ => Set.indicator {y : ℝ | ∀ m : ℤ, δ ≤ |y - x - m|} f y) x
    (a := gradBLo N ℓ γ x - x) (b := gradBHi N ℓ γ x - x)
  simp only [sub_add_cancel] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro v _
  simp only
  by_cases hv : ∀ m : ℤ, δ ≤ |v - m|
  · have hv' : v + x ∈ {y : ℝ | ∀ m : ℤ, δ ≤ |y - x - m|} := by
      intro m
      rw [show v + x - x - m = v - m by ring]
      exact hv m
    rw [Set.indicator_of_mem hv', Set.indicator_of_mem (show v ∈ gradAllowed δ from hv), add_comm v x]
  · have hv' : v + x ∉ {y : ℝ | ∀ m : ℤ, δ ≤ |y - x - m|} := by
      intro h'
      apply hv
      intro m
      have := h' m
      rwa [show v + x - x - m = v - m by ring] at this
    rw [Set.indicator_of_notMem hv', Set.indicator_of_notMem (show v ∉ gradAllowed δ from hv)]

/-- A limit of the `v`-frame truncations is a limit of the `y`-frame truncations. -/
lemma tendsto_gradPV_integral_of_tendsto (N : ℕ+) (ℓ γ x : ℝ) {f : ℝ → ℝ} {L : ℝ}
    (h : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
      (gradAllowed δ).indicator (fun v => f (x + v)) v) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun δ : ℝ => ∫ y in gradBLo N ℓ γ x..gradBHi N ℓ γ x,
      Set.indicator {y : ℝ | ∀ m : ℤ, δ ≤ |y - x - m|} f y) (𝓝[>] 0) (𝓝 L) := by
  simp_rw [gradPV_integral_eq_vframe]
  exact h

/-- The principal value over `B` in the `v`-frame: a limit of the truncated integrals of `f(x + v)`
on the allowed set determines `gradPV`. -/
lemma gradPV_eq_of_tendsto (N : ℕ+) (ℓ γ x : ℝ) {f : ℝ → ℝ} {L : ℝ}
    (h : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
      (gradAllowed δ).indicator (fun v => f (x + v)) v) (𝓝[>] 0) (𝓝 L)) :
    gradPV N ℓ γ x f = L := by
  unfold gradPV
  simp_rw [gradPV_integral_eq_vframe]
  exact h.limUnder_eq

/-- The `Φ` term of the closed form: `Φ(x) = ∫_{-1/2}^{1/2} ψ'((x+v)/ℓ) g(v) dv`. -/
def gradPhi (s : ℝ) (ψ : ℝ → ℝ) (ℓ x : ℝ) : ℝ :=
  ∫ v in (-1 / 2 : ℝ)..(1 / 2), deriv ψ ((x + v) / ℓ) * hurwitzKernel s v

/-- The boundary term of the partial window: `BT(x) = -ℓ ψ(x/ℓ) (g(t-x) - g(-t-x))`. -/
def gradBTpart (s : ℝ) (ψ : ℝ → ℝ) (ℓ t x : ℝ) : ℝ :=
  -ℓ * ψ (x / ℓ) * (hurwitzKernel s (t - x) - hurwitzKernel s (-t - x))

/-- `ψ(z/ℓ) = 0` at the two endpoints `±t` of the partial window. -/
lemma psi_zero_at_pm_t {ψ : ℝ → ℝ} {ℓ t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) :
    ψ (t / ℓ) = 0 ∧ ψ (-t / ℓ) = 0 := by
  constructor
  · apply hsupp
    intro m
    have h := le_abs_add_int ht ht2 (-m)
    rw [show t + ((-m : ℤ) : ℝ) = t - m by push_cast; ring] at h
    linarith
  · apply hsupp
    intro m
    have h := le_abs_add_int ht ht2 m
    rw [show -t - m = -(t + m) by ring, abs_neg]
    linarith

/-- The closed form of the partial-window background integral (with the
principal value written out): `J(x) = BT(x) - Φ(x)`. -/
theorem gradBackground_partial_closed {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) (x : ℝ) :
    ∫ v in (-t - x)..(t - x), gradD ψ ℓ x v * deriv (hurwitzKernel s) v
      = gradBTpart s ψ ℓ t x - gradPhi s ψ ℓ x := by
  have hab : -t - x < t - x := by linarith
  have ha : (∃ m : ℤ, -t - x = m) → ∀ᶠ v in 𝓝 (-t - x), gradD ψ ℓ x v = 0 := by
    rintro ⟨n, hn⟩
    refine gradD_eventually_zero hℓ0.ne' ht hsupp ?_ ?_
    · exact far_of_endpoint ht ht2 (Or.inl ⟨n, by linarith⟩)
    · intro m
      rw [show x + (-t - x) - m = -(t + m) by ring, abs_neg]
      exact le_abs_add_int ht ht2 m
  have hb : (∃ m : ℤ, t - x = m) → ∀ᶠ v in 𝓝 (t - x), gradD ψ ℓ x v = 0 := by
    rintro ⟨n, hn⟩
    refine gradD_eventually_zero hℓ0.ne' ht hsupp ?_ ?_
    · exact far_of_endpoint ht ht2 (Or.inr ⟨n, by linarith⟩)
    · intro m
      rw [show x + (t - x) - m = t + ((-m : ℤ) : ℝ) by push_cast; ring]
      exact le_abs_add_int ht ht2 (-m)
  rw [integral_gradD_mul_eq_formula hψ hℓ0 hp hs0 hs1 x hab ha hb,
    integral_deriv_psi_mul_eq_period hψ hℓ0 hp hs0 hs1 ht hsupp ht2 x]
  obtain ⟨hpt, hmt⟩ := psi_zero_at_pm_t ht ht2 hsupp
  have hDb : gradD ψ ℓ x (t - x) = -ℓ * ψ (x / ℓ) := by
    unfold gradD
    rw [show x + (t - x) = t by ring, hpt]
    ring
  have hDa : gradD ψ ℓ x (-t - x) = -ℓ * ψ (x / ℓ) := by
    unfold gradD
    rw [show x + (-t - x) = -t by ring, hmt]
    ring
  rw [hDb, hDa]
  unfold gradBTpart gradPhi
  ring

/-- The closed form of the full-window background integral: `J(x) = -Φ(x)`. -/
theorem gradBackground_full_closed {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    ∫ v in (-1 / 2 : ℝ)..(1 / 2), gradD ψ ℓ x v * deriv (hurwitzKernel s) v = -gradPhi s ψ ℓ x := by
  have hab : (-1 / 2 : ℝ) < 1 / 2 := by norm_num
  have hnint : ∀ c : ℝ, (c = -1 / 2 ∨ c = 1 / 2) → ¬ ∃ m : ℤ, c = m := by
    rintro c hc ⟨m, hm⟩
    rcases hc with hc | hc <;> rw [hc] at hm
    · have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
      have h3 : (2 * m : ℤ) = -1 := by exact_mod_cast h2
      omega
    · have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
      have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
      omega
  have hA : (∃ m : ℤ, (-1 / 2 : ℝ) = m) → ∀ᶠ v in 𝓝 (-1 / 2 : ℝ), gradD ψ ℓ x v = 0 :=
    fun h => absurd h (hnint _ (Or.inl rfl))
  have hB : (∃ m : ℤ, (1 / 2 : ℝ) = m) → ∀ᶠ v in 𝓝 (1 / 2 : ℝ), gradD ψ ℓ x v = 0 :=
    fun h => absurd h (hnint _ (Or.inr rfl))
  rw [integral_gradD_mul_eq_formula hψ hℓ0 hp hs0 hs1 x hab hA hB]
  have hper : gradD ψ ℓ x (1 / 2) = gradD ψ ℓ x (-1 / 2) := by
    have h := gradD_periodic hp x (-1 / 2)
    rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
    exact h
  have hgeven : hurwitzKernel s (-1 / 2) = hurwitzKernel s (1 / 2) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, hurwitzKernel_neg']
  rw [hper, hgeven]
  unfold gradPhi
  ring

/-- The family `Φ_φ(x) = ∫_{-1/2}^{1/2} φ((x+v)/ℓ) g(v) dv`. `gradPhi` is the case `φ = ψ'`. -/
def gradPhiFam (s : ℝ) (φ : ℝ → ℝ) (ℓ x : ℝ) : ℝ :=
  ∫ v in (-1 / 2 : ℝ)..(1 / 2), φ ((x + v) / ℓ) * hurwitzKernel s v

lemma gradPhi_eq_fam (s : ℝ) (ψ : ℝ → ℝ) (ℓ x : ℝ) : gradPhi s ψ ℓ x = gradPhiFam s (deriv ψ) ℓ x :=
  rfl

/-- Differentiation of the family under the integral sign, on the fixed interval `[-1/2, 1/2]`. -/
lemma hasDerivAt_gradPhiFam {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {ℓ : ℝ} (_hℓ : ℓ ≠ 0) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (x0 : ℝ) :
    HasDerivAt (fun x => gradPhiFam s φ ℓ x)
      (∫ v in (-1 / 2 : ℝ)..(1 / 2), deriv φ ((x0 + v) / ℓ) * (1 / ℓ) * hurwitzKernel s v) x0 := by
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hgI : IntervalIntegrable (hurwitzKernel s) volume (-1 / 2) (1 / 2) :=
    hurwitzKernel_intervalIntegrable_all hs0 hs1 _ _
  have hcont2 : Continuous (fun p : ℝ × ℝ => deriv φ ((p.1 + p.2) / ℓ)) :=
    hdc.comp (by fun_prop)
  obtain ⟨M0, hM0⟩ := ((isCompact_closedBall x0 1).prod
    (isCompact_Icc (a := (-1 / 2 : ℝ)) (b := 1 / 2))).exists_bound_of_continuousOn
    hcont2.continuousOn
  set M : ℝ := max M0 0 with hM
  have hM0nn : 0 ≤ M := le_max_right _ _
  -- continuity in `v` of the coefficients, at each fixed lift
  have hcoef : ∀ x : ℝ, Continuous (fun v : ℝ => deriv φ ((x + v) / ℓ)) := fun x =>
    hdc.comp (by fun_prop)
  have hcoefd : ∀ x : ℝ, Continuous (fun v : ℝ => deriv φ ((x + v) / ℓ) * (1 / ℓ)) :=
    fun x => (hcoef x).mul continuous_const
  have hFint : ∀ x : ℝ, IntervalIntegrable (fun v : ℝ => φ ((x + v) / ℓ) * hurwitzKernel s v)
      volume (-1 / 2) (1 / 2) := by
    intro x
    have hc : Continuous (fun v : ℝ => φ ((x + v) / ℓ)) :=
      (hφ.continuous).comp (by fun_prop)
    exact hgI.continuousOn_mul hc.continuousOn
  have hF'int : IntervalIntegrable (fun v : ℝ => deriv φ ((x0 + v) / ℓ) * (1 / ℓ) * hurwitzKernel s v)
      volume (-1 / 2) (1 / 2) := hgI.continuousOn_mul (hcoefd x0).continuousOn
  have hbdint : IntervalIntegrable (fun v : ℝ => M * |1 / ℓ| * ‖hurwitzKernel s v‖) volume
      (-1 / 2) (1 / 2) := hgI.norm.const_mul _
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun (x : ℝ) (v : ℝ) => φ ((x + v) / ℓ) * hurwitzKernel s v)
    (F' := fun (x : ℝ) (v : ℝ) => deriv φ ((x + v) / ℓ) * (1 / ℓ) * hurwitzKernel s v)
    (x₀ := x0) (s := Metric.ball x0 1)
    (bound := fun v : ℝ => M * |1 / ℓ| * ‖hurwitzKernel s v‖)
    (a := -1 / 2) (b := 1 / 2) (Metric.ball_mem_nhds x0 one_pos)
    (Eventually.of_forall fun x => by
      rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
      exact (hFint x).1.aestronglyMeasurable)
    (hFint x0)
    (by
      rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
      exact (hF'int.1.aestronglyMeasurable))
    (ae_of_all _ fun v hv x hx => by
      rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hv
      have hvI : v ∈ Icc (-1 / 2 : ℝ) (1 / 2) := ⟨hv.1.le, hv.2⟩
      have hxc : x ∈ Metric.closedBall x0 1 := Metric.ball_subset_closedBall hx
      have h1 : ‖deriv φ ((x + v) / ℓ)‖ ≤ M := (hM0 (x, v) ⟨hxc, hvI⟩).trans (le_max_left M0 0)
      show ‖deriv φ ((x + v) / ℓ) * (1 / ℓ) * hurwitzKernel s v‖ ≤ M * |1 / ℓ| * ‖hurwitzKernel s v‖
      rw [norm_mul, norm_mul, Real.norm_eq_abs (1 / ℓ)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
        (norm_nonneg _))
    hbdint
    (ae_of_all _ fun v _ x _ => by
      have hd : HasDerivAt (fun x : ℝ => (x + v) / ℓ) (1 / ℓ) x := by
        simpa using ((hasDerivAt_id x).add_const v).div_const ℓ
      have hφd : HasDerivAt φ (deriv φ ((x + v) / ℓ)) ((x + v) / ℓ) :=
        ((hφ.differentiable one_ne_zero) _).hasDerivAt
      exact (hφd.comp x hd).mul_const (hurwitzKernel s v))
  exact key.2

/-- The derivative of the family is `(1/ℓ)` times the family of `φ'`. -/
lemma deriv_gradPhiFam {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    deriv (fun x => gradPhiFam s φ ℓ x) x = (1 / ℓ) * gradPhiFam s (deriv φ) ℓ x := by
  rw [(hasDerivAt_gradPhiFam hφ hℓ hs0 hs1 x).deriv, gradPhiFam, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  simp only
  ring

/-- The family is smooth in `x`, for every order `n`, when `φ` is smooth. -/
lemma contDiff_gradPhiFam_nat {ℓ : ℝ} (hℓ : ℓ ≠ 0) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ n : ℕ, ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → ContDiff ℝ n (fun x => gradPhiFam s φ ℓ x) := by
  intro n
  induction n with
  | zero =>
    intro φ hφ
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_gradPhiFam (hφ.of_le (by simp)) hℓ hs0 hs1 x).continuousAt
  | succ n ih =>
    intro φ hφ
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hdiff : Differentiable ℝ (fun x => gradPhiFam s φ ℓ x) := fun x =>
      (hasDerivAt_gradPhiFam hφ1 hℓ hs0 hs1 x).differentiableAt
    have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
    have hder : ContDiff ℝ n (deriv (fun x => gradPhiFam s φ ℓ x)) := by
      have : deriv (fun x => gradPhiFam s φ ℓ x) = fun x => (1 / ℓ) * gradPhiFam s (deriv φ) ℓ x :=
        funext fun x => deriv_gradPhiFam hφ1 hℓ hs0 hs1 x
      rw [this]
      exact contDiff_const.mul (ih (deriv φ) hφd)
    push_cast
    exact contDiff_succ_iff_deriv.2 ⟨hdiff, fun h => absurd h (by simp), hder⟩

/-- The family is smooth in `x` when `φ` is smooth. -/
lemma contDiff_gradPhiFam {ℓ : ℝ} (hℓ : ℓ ≠ 0) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (fun x => gradPhiFam s φ ℓ x) :=
  contDiff_infty.2 fun n => contDiff_gradPhiFam_nat hℓ hs0 hs1 n φ hφ

/-- The derivative of `BT`, in product form: `BT'(x) = -ψ'(x/ℓ)(g(t-x)-g(-t-x)) + ℓψ(x/ℓ)(G(t-x)-G(-t-x))`
(with `G = deriv g`). -/
def gradBTpartDeriv (s : ℝ) (ψ : ℝ → ℝ) (ℓ t x : ℝ) : ℝ :=
  -deriv ψ (x / ℓ) * (hurwitzKernel s (t - x) - hurwitzKernel s (-t - x))
    + (-ℓ * ψ (x / ℓ)) * (-deriv (hurwitzKernel s) (t - x) + deriv (hurwitzKernel s) (-t - x))

/-- Near a point with an integer endpoint, `BT` vanishes: `ψ(·/ℓ)` vanishes on a neighbourhood. -/
lemma gradBTpart_eventually_zero {ψ : ℝ → ℝ} {ℓ t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) {x : ℝ}
    (hx : (∃ n : ℤ, x = -t - n) ∨ (∃ n : ℤ, x = t - n)) :
    ∀ᶠ y in 𝓝 x, ψ (y / ℓ) = 0 :=
  eventually_psi_zero_near ht hsupp (far_of_endpoint ht ht2 hx)

/-- A real number that is not an integer has nonzero image in the circle. -/
lemma coe_ne_zero_of_forall_ne_int {r : ℝ} (h : ∀ n : ℤ, r ≠ n) : (r : UnitAddCircle) ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
  rw [zsmul_eq_mul, mul_one] at hn
  exact h n hn.symm

/-- `BT` is smooth, as a function of the lift. -/
lemma contDiffAt_gradBTpart {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ t : ℝ} (ht : 0 < t)
    (ht2 : t ≤ 1 / 2) (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    ContDiffAt ℝ ∞ (fun y => gradBTpart s ψ ℓ t y) x := by
  by_cases hx : (∃ n : ℤ, x = -t - n) ∨ (∃ n : ℤ, x = t - n)
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [gradBTpart_eventually_zero ht ht2 hsupp hx] with y hy
    unfold gradBTpart
    rw [hy]
    ring
  · simp only [not_or, not_exists] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hne1 : ((t - x : ℝ) : UnitAddCircle) ≠ 0 :=
      coe_ne_zero_of_forall_ne_int fun n h => hx2 n (by linarith)
    have hne2 : ((-t - x : ℝ) : UnitAddCircle) ≠ 0 :=
      coe_ne_zero_of_forall_ne_int fun n h => hx1 n (by linarith)
    have hg1 : ContDiffAt ℝ ∞ (hurwitzKernel s) (t - x) :=
      ((gradSplit_contDiffOn_kernel s hs0 hs1).contDiffAt (gradSplit_isOpen_nonInt.mem_nhds hne1))
    have hg2 : ContDiffAt ℝ ∞ (hurwitzKernel s) (-t - x) :=
      ((gradSplit_contDiffOn_kernel s hs0 hs1).contDiffAt (gradSplit_isOpen_nonInt.mem_nhds hne2))
    have hgc1 : ContDiffAt ℝ ∞ (fun y : ℝ => hurwitzKernel s (t - y)) x :=
      hg1.comp x (contDiffAt_const.sub contDiffAt_id)
    have hgc2 : ContDiffAt ℝ ∞ (fun y : ℝ => hurwitzKernel s (-t - y)) x :=
      hg2.comp x (contDiffAt_const.sub contDiffAt_id)
    have hpsi : ContDiffAt ℝ ∞ (fun y : ℝ => ψ (y / ℓ)) x :=
      (hψ.contDiffAt).comp x (contDiffAt_id.div_const ℓ)
    unfold gradBTpart
    have h := ((contDiffAt_const (c := -ℓ)).mul hpsi).mul (hgc1.sub hgc2)
    simpa [mul_assoc] using h

/-- The derivative of `BT` at every lift, in the product form `gradBTpartDeriv`. -/
lemma hasDerivAt_gradBTpart {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ t : ℝ} (hℓ : ℓ ≠ 0) (ht : 0 < t)
    (ht2 : t ≤ 1 / 2) (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    HasDerivAt (fun y => gradBTpart s ψ ℓ t y) (gradBTpartDeriv s ψ ℓ t x) x := by
  by_cases hx : (∃ n : ℤ, x = -t - n) ∨ (∃ n : ℤ, x = t - n)
  · have hz := gradBTpart_eventually_zero ht ht2 hsupp hx
    have hψx : ψ (x / ℓ) = 0 := hz.self_of_nhds
    have hdψx : deriv ψ (x / ℓ) = 0 :=
      deriv_psi_zero_of_eventually hℓ hz ((hψ.differentiable (by simp)) _)
    have hval : gradBTpartDeriv s ψ ℓ t x = 0 := by
      unfold gradBTpartDeriv
      rw [hψx, hdψx]
      ring
    rw [hval]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hz] with y hy
    unfold gradBTpart
    rw [hy]
    ring
  · simp only [not_or, not_exists] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hne1 : ((t - x : ℝ) : UnitAddCircle) ≠ 0 :=
      coe_ne_zero_of_forall_ne_int fun n h => hx2 n (by linarith)
    have hne2 : ((-t - x : ℝ) : UnitAddCircle) ≠ 0 :=
      coe_ne_zero_of_forall_ne_int fun n h => hx1 n (by linarith)
    have hdg : ∀ r : ℝ, ((r : UnitAddCircle) ≠ 0) → HasDerivAt (hurwitzKernel s) (deriv (hurwitzKernel s) r) r :=
      fun r hr => (((gradSplit_contDiffOn_kernel s hs0 hs1).contDiffAt
        (gradSplit_isOpen_nonInt.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
    have hd1 : HasDerivAt (fun y => hurwitzKernel s (t - y))
        (-deriv (hurwitzKernel s) (t - x)) x := by
      have h : HasDerivAt (hurwitzKernel s ∘ fun y : ℝ => t - y)
          (deriv (hurwitzKernel s) (t - x) * (-1)) x :=
        (hdg (t - x) hne1).comp x ((hasDerivAt_id x).const_sub t)
      rw [mul_neg_one] at h
      exact h
    have hd2 : HasDerivAt (fun y => hurwitzKernel s (-t - y))
        (-deriv (hurwitzKernel s) (-t - x)) x := by
      have h : HasDerivAt (hurwitzKernel s ∘ fun y : ℝ => -t - y)
          (deriv (hurwitzKernel s) (-t - x) * (-1)) x :=
        (hdg (-t - x) hne2).comp x ((hasDerivAt_id x).const_sub (-t))
      rw [mul_neg_one] at h
      exact h
    have hψd : HasDerivAt (fun y : ℝ => ψ (y / ℓ)) (deriv ψ (x / ℓ) * (1 / ℓ)) x := by
      have hlin : HasDerivAt (fun y : ℝ => y / ℓ) (1 / ℓ) x := by
        simpa using (hasDerivAt_id x).div_const ℓ
      exact ((hψ.differentiable (by simp)) _).hasDerivAt.comp x hlin
    have h := (hψd.const_mul (-ℓ)).mul (hd1.sub hd2)
    refine h.congr_deriv ?_
    unfold gradBTpartDeriv
    simp only [Pi.sub_apply]
    field_simp
    ring

/-- The period trick for an arbitrary coefficient `φ` of the lift `(x+v)/ℓ`: it is one-periodic in `v`
and vanishes on the complementary arc. -/
lemma integral_coeff_mul_eq_period {φ : ℝ → ℝ} {ℓ : ℝ} (_hℓ : 0 < ℓ)
    (hφp : Function.Periodic φ (1 / ℓ)) (hφc : Continuous φ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {t : ℝ} (_ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hφz : ∀ z : ℝ, z ∈ Icc t (1 - t) → φ (z / ℓ) = 0) (x : ℝ) :
    ∫ v in (-t - x)..(t - x), φ ((x + v) / ℓ) * hurwitzKernel s v
      = ∫ v in (-1 / 2 : ℝ)..(1 / 2), φ ((x + v) / ℓ) * hurwitzKernel s v := by
  set f : ℝ → ℝ := fun v => φ ((x + v) / ℓ) * hurwitzKernel s v with hf
  have hper : Function.Periodic f 1 := by
    intro v
    simp only [hf]
    rw [show (x + (v + 1)) / ℓ = (x + v) / ℓ + 1 / ℓ by ring, hφp ((x + v) / ℓ),
      hurwitzKernel_periodic s v]
  have hint : ∀ c d : ℝ, IntervalIntegrable f volume c d := fun c d =>
    (hurwitzKernel_intervalIntegrable_all hs0 hs1 c d).continuousOn_mul
      ((hφc.comp (by fun_prop : Continuous fun v : ℝ => (x + v) / ℓ)).continuousOn)
  have hshift := hper.intervalIntegral_add_eq (-t - x) (-1 / 2)
  have hsplit : ∫ v in (-t - x)..((-t - x) + 1), f v
      = (∫ v in (-t - x)..(t - x), f v) + ∫ v in (t - x)..((-t - x) + 1), f v :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have hzero : ∫ v in (t - x)..((-t - x) + 1), f v = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun v hv => ?_),
      intervalIntegral.integral_zero]
    rw [uIcc_of_le (by linarith)] at hv
    have hz : x + v ∈ Icc t (1 - t) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    simp only [hf]
    rw [show (x + v) / ℓ = (x + v) / ℓ from rfl]
    have hz' : (x + v) ∈ Icc t (1 - t) := hz
    rw [hφz (x + v) hz', zero_mul]
  have h1 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [h1] at hshift
  rw [hsplit, hzero, add_zero] at hshift
  exact hshift

/-- `ψ''` vanishes on `[t, 1 - t]` (`0 < t ≤ 1/2`) when `ψ` vanishes away from the integers. -/
lemma deriv_deriv_psi_zero_of_mem_Icc {ψ : ℝ → ℝ} {ℓ t : ℝ} (hℓ : ℓ ≠ 0) (ht : 0 < t)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) {z : ℝ}
    (hz : z ∈ Icc t (1 - t)) : deriv (deriv ψ) (z / ℓ) = 0 := by
  have hfar : ∀ m : ℤ, t ≤ |z - m| := by
    intro m
    rcases le_or_gt m 0 with h | h
    · have hm : (m : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith [hz.1])]
      linarith [hz.1]
    · have hm : (1 : ℝ) ≤ m := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith [hz.2])]
      linarith [hz.2]
  have hψ0 : ∀ᶠ y in 𝓝 z, ψ (y / ℓ) = 0 := eventually_psi_zero_near ht hsupp hfar
  -- in the variable `u = y / ℓ`, `ψ` vanishes near `z / ℓ`
  have hc : Tendsto (fun u : ℝ => u * ℓ) (𝓝 (z / ℓ)) (𝓝 z) := by
    have h : Tendsto (fun u : ℝ => u * ℓ) (𝓝 (z / ℓ)) (𝓝 ((z / ℓ) * ℓ)) :=
      ((continuous_id.mul continuous_const : Continuous fun u : ℝ => u * ℓ)).tendsto (z / ℓ)
    rwa [div_mul_cancel₀ _ hℓ] at h
  have hψu : ψ =ᶠ[𝓝 (z / ℓ)] fun _ => (0 : ℝ) := by
    filter_upwards [hc.eventually hψ0] with u hu
    simpa [mul_div_assoc, mul_div_cancel_right₀ _ hℓ] using hu
  have hdeq : deriv ψ =ᶠ[𝓝 (z / ℓ)] fun _ => (0 : ℝ) := by
    have h := hψu.deriv
    simpa using h
  exact (hdeq.deriv_eq).trans (deriv_const _ 0)

end

end Riesz1
