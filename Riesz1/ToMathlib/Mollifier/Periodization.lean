/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Mollifier.Multiplier
public import Riesz1.ToMathlib.CircleBasics
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

/-!
# Periodized mollifier and regularization on the circle

For a circle mollifier `ρ` and a scale `0 < h ≤ 1`, the periodized mollifier
`ρ_h(x) = ∑_{n ∈ ℤ} h⁻¹ ρ((x + n) / h)` is a continuous function on the unit circle
`UnitAddCircle`. Its sum is locally finite, and for `h ≤ 1` at most one term is nonzero at each
point, so it is bounded by `h⁻¹ · sup|ρ|`.

Main results:
* `circleMollifier_coe`: the value at `t : ℝ` is the series `∑' n, h⁻¹ ρ((t + n) / h)`.
* `norm_circleMollifier_le`: the uniform bound `|ρ_h| ≤ h⁻¹ sup|ρ|`.
* `fourierCoeff_circleMollifier`: the `k`-th Fourier coefficient of `ρ_h` is `ρ̂(h k)`.
* `circleRegularize`: the convolution `ξ ∗ ρ_h` of an `L²` function with `ρ_h`.
* `memLp_circleRegularize`: the convolution is again in `L²`.
* `fourierCoeff_circleRegularize`: the convolution multiplies Fourier coefficients by `ρ_h`'s.
-/

public section

open MeasureTheory Real
open scoped FourierTransform ContDiff

namespace Riesz1

/-- The rescaled mollifier `t ↦ h⁻¹ ρ(t / h)` as a continuous function with values in `ℂ`. -/
@[expose] noncomputable def kernelCont (ρ : ℝ → ℝ) (h : {h : ℝ // 0 < h}) (hρ : Continuous ρ) : C(ℝ, ℂ) :=
  ⟨fun t => ((h.1⁻¹ * ρ (t / h.1) : ℝ) : ℂ), by fun_prop⟩

/-- The periodized mollifier `ρ_h` on the unit circle, `x ↦ ∑_{n ∈ ℤ} h⁻¹ ρ((x + n) / h)`, for a
scale `h > 0`. It is the periodization with period one of `kernelCont ρ h`. -/
@[expose] noncomputable def circleMollifier (ρ : ℝ → ℝ) (h : {h : ℝ // 0 < h}) (hρ : Continuous ρ) :
    UnitAddCircle → ℂ :=
  Function.Periodic.lift ((kernelCont ρ h hρ).periodic_tsum_comp_add_zsmul 1)

/-- The convolution `ξ ∗ ρ_h` on the unit circle of an `L²` function, `x ↦ ∫ ξ(y) ρ_h(x - y) dy`,
with respect to the arclength measure `volume`, which has total mass one. -/
@[expose] noncomputable def circleRegularize (ρ : ℝ → ℝ) (h : {h : ℝ // 0 < h}) (hρ : Continuous ρ)
    (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) : UnitAddCircle → ℂ :=
  fun x => ∫ y, ξ.1 y * circleMollifier ρ h hρ (x - y)

variable {ρ : ℝ → ℝ}

/-- A point at distance at least one from the origin lies outside the support of `ρ(· / h)`,
when `0 < h ≤ 1`. -/
lemma mollifier_div_eq_zero_of_one_le (hρ : IsCircleMollifier ρ) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) {t : ℝ} (ht : 1 ≤ |t|) : ρ (t / h) = 0 := by
  by_contra hne
  have h1 := hρ.abs_lt_of_ne_zero hne
  rw [abs_div, abs_of_pos hh] at h1
  have h2 : 1 ≤ |t| / h := by
    rw [le_div_iff₀ hh]
    linarith
  linarith

/-- If `ρ((s) / h) ≠ 0` then `|s| < h / 2`. -/
lemma abs_lt_of_mollifier_ne_zero (hρ : IsCircleMollifier ρ) {h : ℝ} (hh : 0 < h) {s : ℝ}
    (hs : ρ (s / h) ≠ 0) : |s| < h / 2 := by
  have h1 := hρ.abs_lt_of_ne_zero hs
  rw [abs_div, abs_of_pos hh, div_lt_iff₀ hh] at h1
  linarith

/-- The summands of the periodization vanish outside a finite set of integers, uniformly for
`t` in a compact set, so the family of their sup-norms is summable. -/
lemma summable_restrict_norm (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h}) (hh1 : h.1 ≤ 1)
    (K : TopologicalSpace.Compacts ℝ) :
    Summable fun n : ℤ => ‖((kernelCont ρ h hρ.continuous).comp
      (ContinuousMap.addRight (n • (1 : ℝ)))).restrict (K : Set ℝ)‖ := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_ge (R + 1)
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) fun n hn => ?_
  have hn' : (N : ℝ) < |(n : ℝ)| := by
    have hlt : (N : ℤ) < |n| := by
      by_contra hc
      exact hn (Finset.mem_Icc.mpr (abs_le.mp (not_lt.mp hc)))
    have h3 : ((N : ℤ) : ℝ) < ((|n| : ℤ) : ℝ) := by exact_mod_cast hlt
    rw [Int.cast_abs] at h3
    simpa using h3
  refine norm_eq_zero.mpr (ContinuousMap.ext fun x => ?_)
  have hxR := hR x.2
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hxR
  have hfar : 1 ≤ |(x : ℝ) + n| := by
    have hx := abs_le.mp hxR
    rcases abs_cases ((x : ℝ) + n) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (n : ℝ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      linarith [hx.1, hx.2]
  simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    kernelCont, ContinuousMap.coe_mk, zsmul_eq_mul, mul_one, ContinuousMap.zero_apply]
  rw [mollifier_div_eq_zero_of_one_le hρ h.2 hh1 hfar]
  simp

/-- The periodization is a sum of a locally summable family of continuous functions. -/
lemma summable_kernel (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h}) (hh1 : h.1 ≤ 1) :
    Summable fun n : ℤ => (kernelCont ρ h hρ.continuous).comp
      (ContinuousMap.addRight (n • (1 : ℝ))) :=
  ContinuousMap.summable_of_locally_summable_norm fun K => summable_restrict_norm hρ h hh1 K

/-- The value of the periodized mollifier at a real point is the series `∑_n h⁻¹ ρ((t + n) / h)`. -/
lemma circleMollifier_coe (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h}) (hh1 : h.1 ≤ 1)
    (t : ℝ) :
    circleMollifier ρ h hρ.continuous (t : UnitAddCircle) =
      ∑' n : ℤ, ((h.1⁻¹ * ρ ((t + n) / h.1) : ℝ) : ℂ) := by
  unfold circleMollifier
  rw [Function.Periodic.lift_coe, ← ContinuousMap.tsum_apply (summable_kernel hρ h hh1)]
  congr 1
  funext n
  simp [kernelCont, zsmul_eq_mul]

/-- The periodized mollifier is continuous on the circle. -/
lemma continuous_circleMollifier (hρ : Continuous ρ) (h : {h : ℝ // 0 < h}) :
    Continuous (circleMollifier ρ h hρ) :=
  continuous_coinduced_dom.mpr (map_continuous _)

/-- Uniform bound: at most one term of the periodization is nonzero when `h ≤ 1`, so
`|ρ_h| ≤ h⁻¹ C` for a bound `C` of `|ρ|`. -/
lemma exists_bound_circleMollifier (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h})
    (hh1 : h.1 ≤ 1) :
    ∃ C : ℝ, ∀ x : UnitAddCircle, ‖circleMollifier ρ h hρ.continuous x‖ ≤ h.1⁻¹ * C := by
  obtain ⟨M, hM⟩ := hρ.continuous.bounded_above_of_compact_support hρ.hasCompactSupport
  refine ⟨M, fun x => ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    rw [circleMollifier_coe hρ h hh1]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hinv : 0 < h.1⁻¹ := inv_pos.mpr h.2
    by_cases hex : ∃ n₀ : ℤ, ρ ((t + n₀) / h.1) ≠ 0
    · obtain ⟨n₀, hn₀⟩ := hex
      have hvanish : ∀ m : ℤ, m ≠ n₀ → ((h.1⁻¹ * ρ ((t + m) / h.1) : ℝ) : ℂ) = 0 := by
        intro m hm
        have hz : ρ ((t + m) / h.1) = 0 := by
          by_contra hc
          have h1 := abs_lt_of_mollifier_ne_zero hρ h.2 hc
          have h2 := abs_lt_of_mollifier_ne_zero hρ h.2 hn₀
          have h3 : |((m - n₀ : ℤ) : ℝ)| < 1 := by
            push_cast
            calc |(m : ℝ) - n₀| = |(t + m) - (t + n₀)| := by congr 1; ring
              _ ≤ |t + m| + |t + n₀| := abs_sub _ _
              _ < h.1 := by linarith
              _ ≤ 1 := hh1
          have h4 : m - n₀ = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast h3)
          exact hm (sub_eq_zero.mp h4)
        rw [hz, mul_zero, Complex.ofReal_zero]
      rw [tsum_eq_single n₀ hvanish, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos hinv]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hM _) hinv.le
    · push Not at hex
      have hzero : ∀ n : ℤ, ((h.1⁻¹ * ρ ((t + n) / h.1) : ℝ) : ℂ) = 0 := fun n => by
        rw [hex n, mul_zero, Complex.ofReal_zero]
      simp only [hzero, tsum_zero, norm_zero]
      exact mul_nonneg hinv.le hM0

/-- The `k`-th Fourier coefficient on the unit circle as an integral against `volume`. -/
lemma fourierCoeff_eq_volume (f : UnitAddCircle → ℂ) (k : ℤ) :
    fourierCoeff f k = ∫ x, fourier (-k) x * f x := by
  rw [fourierCoeff, AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  simp only [smul_eq_mul]

/-- Shift of the argument of a Fourier mode on the unit circle. -/
lemma fourier_add_arg (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- Rescaling identity: the transform of `t ↦ h⁻¹ ρ(t / h)` at `w` equals `ρ̂(h w)`. -/
lemma fourier_kernel_eq (ρ : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (w : ℝ) :
    𝓕 (fun t : ℝ => ((h⁻¹ * ρ (t / h) : ℝ) : ℂ)) w =
      𝓕 (fun u : ℝ => (ρ u : ℂ)) (h * w) := by
  rw [fourier_real_eq_integral_exp_smul, fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have key := Measure.integral_comp_mul_left (fun v : ℝ =>
    Complex.exp (↑(-2 * π * v * w) * Complex.I) * ((h⁻¹ * ρ (v / h) : ℝ) : ℂ)) h
  have hpt : ∀ x : ℝ, Complex.exp (↑(-2 * π * (h * x) * w) * Complex.I) *
      ((h⁻¹ * ρ (h * x / h) : ℝ) : ℂ) =
        ((h⁻¹ : ℝ) : ℂ) * (Complex.exp (↑(-2 * π * x * (h * w)) * Complex.I) * (ρ x : ℂ)) := by
    intro x
    have e1 : h * x / h = x := by field_simp
    have e2 : -2 * π * (h * x) * w = -2 * π * x * (h * w) := by ring
    rw [e1, e2]
    push_cast
    ring
  simp_rw [hpt] at key
  rw [integral_const_mul, abs_of_pos (inv_pos.mpr hh), Complex.real_smul] at key
  have hne : ((h⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hh.ne')
  exact (mul_left_cancel₀ hne key).symm

/-- The `k`-th Fourier coefficient of the periodized mollifier is `ρ̂(h k)`. -/
lemma fourierCoeff_circleMollifier (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h})
    (hh1 : h.1 ≤ 1) (k : ℤ) :
    fourierCoeff (circleMollifier ρ h hρ.continuous) k = ((mollifierFT ρ (h.1 * k) : ℝ) : ℂ) := by
  have hs : ∀ K : TopologicalSpace.Compacts ℝ, Summable fun n : ℤ =>
      ‖((kernelCont ρ h hρ.continuous).comp (ContinuousMap.addRight (n : ℝ))).restrict
        (K : Set ℝ)‖ := by
    intro K
    simpa only [zsmul_eq_mul, mul_one] using summable_restrict_norm hρ h hh1 K
  unfold circleMollifier
  rw [Real.fourierCoeff_tsum_comp_add hs k]
  simp only [kernelCont, ContinuousMap.coe_mk]
  rw [fourier_kernel_eq ρ h.2 (k : ℝ), mollifierFT_ofReal hρ]

/-- The regularization is in `L²`: it is bounded by `h⁻¹ C ∫ |ξ|`, and it is measurable. -/
lemma memLp_circleRegularize (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h})
    (hh1 : h.1 ≤ 1) (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) :
    MemLp (circleRegularize ρ h hρ.continuous ξ) 2 volume := by
  obtain ⟨C, hC⟩ := exists_bound_circleMollifier hρ h hh1
  have hξ1 : Integrable ξ.1 volume := ξ.2.integrable one_le_two
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, ξ.1 y * circleMollifier ρ h hρ.continuous (x - y))
      volume := by
    refine AEStronglyMeasurable.integral_prod_right'
      (f := fun z : UnitAddCircle × UnitAddCircle =>
        ξ.1 z.2 * circleMollifier ρ h hρ.continuous (z.1 - z.2)) ?_
    exact (ξ.2.aestronglyMeasurable.comp_snd).mul
      ((continuous_circleMollifier hρ.continuous h).comp
        (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  refine MemLp.of_bound hmeas (∫ y, ‖ξ.1 y‖ * (h.1⁻¹ * C)) (Filter.Eventually.of_forall fun x => ?_)
  refine norm_integral_le_of_norm_le (hξ1.norm.mul_const _)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

/-- The convolution multiplies Fourier coefficients: `(ξ ∗ ρ_h)^(k) = ξ^(k) ρ̂(h k)`. -/
lemma fourierCoeff_circleRegularize (hρ : IsCircleMollifier ρ) (h : {h : ℝ // 0 < h})
    (hh1 : h.1 ≤ 1) (ξ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) (k : ℤ) :
    fourierCoeff (circleRegularize ρ h hρ.continuous ξ) k =
      fourierCoeff ξ.1 k * fourierCoeff (circleMollifier ρ h hρ.continuous) k := by
  set P := circleMollifier ρ h hρ.continuous with hP
  obtain ⟨C, hC⟩ := exists_bound_circleMollifier hρ h hh1
  have hPc : Continuous P := continuous_circleMollifier hρ.continuous h
  have hξ1 : Integrable ξ.1 volume := ξ.2.integrable one_le_two
  have hint : Integrable (fun p : UnitAddCircle × UnitAddCircle =>
      fourier (-k) p.1 * (ξ.1 p.2 * P (p.1 - p.2))) (volume.prod volume) := by
    refine Integrable.mono' ((hξ1.norm.comp_snd volume).mul_const (h.1⁻¹ * C)) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact ((fourier (-k)).continuous.comp continuous_fst).aestronglyMeasurable.mul
        (ξ.2.aestronglyMeasurable.comp_snd.mul
          (hPc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)
    · rw [norm_mul, norm_mul, norm_fourier_apply, one_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  set c := ∫ x, fourier (-k) x * P x with hc
  have inner : ∀ y : UnitAddCircle,
      ∫ x, fourier (-k) x * (ξ.1 y * P (x - y)) = ξ.1 y * (fourier (-k) y * c) := by
    intro y
    have hshift : ∫ x, fourier (-k) (x + y) * P (x + y - y) =
        ∫ x, fourier (-k) x * P (x - y) :=
      integral_add_right_eq_self (fun x => fourier (-k) x * P (x - y)) y
    have hF : ∀ x, fourier (-k) (x + y) * P (x + y - y) =
        fourier (-k) y * (fourier (-k) x * P x) := by
      intro x
      rw [fourier_add_arg, add_sub_cancel_right]
      ring
    calc ∫ x, fourier (-k) x * (ξ.1 y * P (x - y))
        = ξ.1 y * ∫ x, fourier (-k) x * P (x - y) := by
          rw [← integral_const_mul]
          congr 1
          funext x
          ring
      _ = ξ.1 y * ∫ x, fourier (-k) (x + y) * P (x + y - y) := by rw [hshift]
      _ = ξ.1 y * ∫ x, fourier (-k) y * (fourier (-k) x * P x) := by simp only [hF]
      _ = ξ.1 y * (fourier (-k) y * c) := by rw [integral_const_mul]
  rw [fourierCoeff_eq_volume, fourierCoeff_eq_volume, fourierCoeff_eq_volume]
  calc ∫ x, fourier (-k) x * circleRegularize ρ h hρ.continuous ξ x
      = ∫ x, ∫ y, fourier (-k) x * (ξ.1 y * P (x - y)) := by
        congr 1
        funext x
        unfold circleRegularize
        rw [integral_const_mul]
    _ = ∫ y, ∫ x, fourier (-k) x * (ξ.1 y * P (x - y)) := integral_integral_swap hint
    _ = ∫ y, ξ.1 y * (fourier (-k) y * c) := by
        congr 1
        funext y
        exact inner y
    _ = ∫ y, (fourier (-k) y * ξ.1 y) * c := by
        congr 1
        funext y
        ring
    _ = (∫ y, fourier (-k) y * ξ.1 y) * c := integral_mul_const _ _

end Riesz1

end
