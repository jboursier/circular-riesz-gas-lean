/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowPVEnds

/-!
# Principal value of `Ψ g''` by truncated integration by parts

For a `C²` coefficient `Ψ` with the second-order cancellation `|Ψ(k + δ) + Ψ(k - δ)| ≤ M δ²` at the
integers `k`, the principal value of `Ψ g''` over `[a, b]` (non-integer endpoints) exists. Its
truncated formula has the boundary term `-G(δ)(Ψ(k-δ) + Ψ(k+δ))` with `G = deriv g`, which tends to
zero because `δ² G(δ) → 0`. The remaining integral `∫ Ψ' G` is a principal value by
`tendsto_truncated_by_parts`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The derivative `G = deriv g` of the kernel is one-periodic. -/
lemma deriv_hurwitzKernel_periodic' (s : ℝ) : Function.Periodic (deriv (hurwitzKernel s)) 1 :=
  fun x => deriv_hurwitzKernel_add_one' s x

/-- `G(k - δ) = -G(δ)` and `G(k + δ) = G(δ)` for an integer `k`. -/
lemma deriv_hurwitzKernel_int_sub (s δ : ℝ) (k : ℤ) :
    deriv (hurwitzKernel s) ((k : ℝ) - δ) = -deriv (hurwitzKernel s) δ := by
  have h := (deriv_hurwitzKernel_periodic' s).int_mul k (-δ)
  rw [show (k : ℝ) - δ = -δ + (k : ℝ) * 1 by ring, h, deriv_hurwitzKernel_neg']

lemma deriv_hurwitzKernel_int_add (s δ : ℝ) (k : ℤ) :
    deriv (hurwitzKernel s) ((k : ℝ) + δ) = deriv (hurwitzKernel s) δ := by
  have h := (deriv_hurwitzKernel_periodic' s).int_mul k δ
  rw [show (k : ℝ) + δ = δ + (k : ℝ) * 1 by ring, h]

/-- `δ² G(δ) → 0` as `δ ↓ 0`, since `|G(δ)| ≤ C δ^{-s-1}`. -/
lemma tendsto_sq_mul_deriv_hurwitzKernel_nhdsGT {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun δ : ℝ => δ ^ 2 * deriv (hurwitzKernel s) δ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := gradSplit_kernel_deriv_bound s hs0 hs1
  have hlim : Tendsto (fun δ : ℝ => C * δ ^ (1 - s)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun δ : ℝ => δ ^ (1 - s)) (𝓝 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const (0 : ℝ) (1 - s) (Or.inr (by linarith))).tendsto
      rwa [Real.zero_rpow (by linarith : (0 : ℝ) < 1 - s).ne'] at h
    simpa using ((hc.const_mul C).mono_left nhdsWithin_le_nhds)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 3 / 4)] with δ hδ
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : |δ| ≤ 3 / 4 := by rw [abs_of_pos hδ0]; exact hδ.2.le
  have h := hb δ (by rw [abs_of_pos hδ0]; exact hδ0) hδ1 1 le_rfl (by norm_num)
  simp only [iteratedDeriv_one, Nat.cast_one, abs_of_pos hδ0] at h
  have hrp : δ ^ (1 - s) = δ ^ 2 * δ ^ (-s - 1) := by
    rw [show (1 : ℝ) - s = (2 : ℕ) + (-s - 1) by push_cast; ring, Real.rpow_add hδ0,
      Real.rpow_natCast]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hδ0 2), hrp]
  calc δ ^ 2 * |deriv (hurwitzKernel s) δ| ≤ δ ^ 2 * (C * δ ^ (-s - 1)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = C * (δ ^ 2 * δ ^ (-s - 1)) := by ring

/-- A Taylor bound for the second symmetric difference of a `C²` function on `(0, R]`. -/
lemma exists_abs_second_diff_le {P : ℝ → ℝ} (hP : ContDiff ℝ 2 P) (x R : ℝ) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, 0 < u → u ≤ R → |P (x + u) + P (x - u) - 2 * P x| ≤ M * u ^ 2 := by
  have hP2 : ContDiff ℝ (1 + 1) P := by norm_num; exact hP
  have hP1 : ContDiff ℝ 1 (deriv P) := ContDiff.deriv' hP2
  have hdd : Continuous (deriv (deriv P)) := hP1.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := x - R) (b := x + R)).exists_bound_of_continuousOn
    hdd.continuousOn
  set M₀ : ℝ := max M 0 with hM₀
  have hM₀nn : 0 ≤ M₀ := le_max_right _ _
  -- the increment of `P'` over a symmetric interval
  have hD : ∀ w : ℝ, 0 ≤ w → w ≤ R →
      |deriv P (x + w) - deriv P (x - w)| ≤ M₀ * (2 * w) := by
    intro w hw0 hwR
    have hsub : Icc (x - w) (x + w) ⊆ Icc (x - R) (x + R) := fun z hz =>
      ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv P) (s := Icc (x - w) (x + w))
      (C := M₀) (x := x - w) (y := x + w)
      (fun z _ => (hP1.differentiable one_ne_zero) z)
      (fun z hz => (hM z (hsub hz)).trans (le_max_left _ _))
      (convex_Icc _ _) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show x + w - (x - w) = 2 * w by ring,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * w)] at h
    exact h
  -- the derivative of `w ↦ φ(w) + c w²`, with `φ(w) = P(x+w) + P(x-w) - 2P(x)`
  have hdφ : ∀ c w : ℝ, HasDerivAt (fun w => P (x + w) + P (x - w) - 2 * P x + c * w ^ 2)
      (deriv P (x + w) - deriv P (x - w) + c * (2 * w)) w := by
    intro c w
    have h1 : HasDerivAt (fun w => P (x + w)) (deriv P (x + w)) w := by
      have := ((hP.differentiable (by norm_num)) (x + w)).hasDerivAt.comp w
        ((hasDerivAt_id w).const_add x)
      rw [mul_one] at this
      exact this
    have h2 : HasDerivAt (fun w => P (x - w)) (-deriv P (x - w)) w := by
      have := ((hP.differentiable (by norm_num)) (x - w)).hasDerivAt.comp w
        ((hasDerivAt_id w).const_sub x)
      rw [mul_neg_one] at this
      exact this
    have h3 : HasDerivAt (fun w : ℝ => c * w ^ 2) (c * (2 * w)) w := by
      have := (hasDerivAt_pow 2 w).const_mul c
      convert this using 1
      push_cast
      ring
    have := ((h1.add h2).sub_const (2 * P x)).add h3
    convert this using 1
  refine ⟨M₀, hM₀nn, fun u hu0 huR => ?_⟩
  have hφ0 : P (x + 0) + P (x - 0) - 2 * P x + (-M₀) * 0 ^ 2 = 0 := by simp; ring
  have hφ0' : P (x + 0) + P (x - 0) - 2 * P x + M₀ * 0 ^ 2 = 0 := by simp; ring
  -- upper bound: `w ↦ φ(w) - M₀ w²` is antitone on `[0, R]`
  have hanti : AntitoneOn (fun w => P (x + w) + P (x - w) - 2 * P x + (-M₀) * w ^ 2) (Icc 0 R) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 R) ?_ ?_ ?_
    · exact fun w _ => (hdφ (-M₀) w).continuousAt.continuousWithinAt
    · exact fun w _ => (hdφ (-M₀) w).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hdφ (-M₀) w).deriv]
      have hb := hD w hw.1.le hw.2.le
      have hb' := (abs_le.1 hb).2
      linarith
  -- lower bound: `w ↦ φ(w) + M₀ w²` is monotone on `[0, R]`
  have hmono : MonotoneOn (fun w => P (x + w) + P (x - w) - 2 * P x + M₀ * w ^ 2) (Icc 0 R) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 R) ?_ ?_ ?_
    · exact fun w _ => (hdφ M₀ w).continuousAt.continuousWithinAt
    · exact fun w _ => (hdφ M₀ w).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hdφ M₀ w).deriv]
      have hb := hD w hw.1.le hw.2.le
      have hb' := (abs_le.1 hb).1
      linarith
  have hu : u ∈ Icc 0 R := ⟨hu0.le, huR⟩
  have h0 : (0 : ℝ) ∈ Icc 0 R := ⟨le_rfl, hR.le⟩
  have hup := hanti h0 hu hu0.le
  have hlo := hmono h0 hu hu0.le
  simp only at hup hlo
  rw [hφ0] at hup
  rw [hφ0'] at hlo
  rw [abs_le]
  constructor <;> nlinarith [hup, hlo]

/-- The second-order cancellation at the integers for `Ψ(v) = ℓ(ψ((x+v)/ℓ) - ψ(x/ℓ))`:
`|Ψ(k+δ) + Ψ(k-δ)| ≤ M δ²` for every integer `k` and `0 < δ < 1`. Periodicity reduces `k ± δ` to `±δ`,
and the Taylor bound applies at `u = δ/ℓ`. -/
lemma second_diff_periodic_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) (x : ℝ) :
    ∃ M : ℝ, ∀ k : ℤ, ∀ δ : ℝ, 0 < δ → δ < 1 →
      |ℓ * (ψ ((x + ((k : ℝ) + δ)) / ℓ) - ψ (x / ℓ))
        + ℓ * (ψ ((x + ((k : ℝ) - δ)) / ℓ) - ψ (x / ℓ))| ≤ M * δ ^ 2 := by
  have hP2 : ContDiff ℝ 2 (fun u : ℝ => ψ (x / ℓ + u)) :=
    hψ.comp (contDiff_const.add contDiff_id)
  obtain ⟨M, -, hM⟩ := exists_abs_second_diff_le hP2 0 (1 / ℓ) (by positivity)
  refine ⟨M / ℓ, fun k δ hδ hδ1 => ?_⟩
  have hk1 : ψ ((x + ((k : ℝ) + δ)) / ℓ) = ψ (x / ℓ + δ / ℓ) := by
    have h := hp.int_mul k (x / ℓ + δ / ℓ)
    rw [show (x + ((k : ℝ) + δ)) / ℓ = x / ℓ + δ / ℓ + (k : ℝ) * (1 / ℓ) by
      field_simp; ring]
    simpa using h
  have hk2 : ψ ((x + ((k : ℝ) - δ)) / ℓ) = ψ (x / ℓ - δ / ℓ) := by
    have h := hp.int_mul k (x / ℓ - δ / ℓ)
    rw [show (x + ((k : ℝ) - δ)) / ℓ = x / ℓ - δ / ℓ + (k : ℝ) * (1 / ℓ) by
      field_simp; ring]
    simpa using h
  have hu := hM (δ / ℓ) (div_pos hδ hℓ) (div_le_div_of_nonneg_right hδ1.le hℓ.le)
  have hu' : |ψ (x / ℓ + δ / ℓ) + ψ (x / ℓ - δ / ℓ) - 2 * ψ (x / ℓ)| ≤ M * (δ / ℓ) ^ 2 := by
    simpa [sub_eq_add_neg] using hu
  rw [hk1, hk2, show ℓ * (ψ (x / ℓ + δ / ℓ) - ψ (x / ℓ)) + ℓ * (ψ (x / ℓ - δ / ℓ) - ψ (x / ℓ))
      = ℓ * (ψ (x / ℓ + δ / ℓ) + ψ (x / ℓ - δ / ℓ) - 2 * ψ (x / ℓ)) by ring,
    abs_mul, abs_of_pos hℓ]
  calc ℓ * |ψ (x / ℓ + δ / ℓ) + ψ (x / ℓ - δ / ℓ) - 2 * ψ (x / ℓ)|
      ≤ ℓ * (M * (δ / ℓ) ^ 2) := mul_le_mul_of_nonneg_left hu' hℓ.le
    _ = M / ℓ * δ ^ 2 := by field_simp

/-- `deriv (deriv g) = iteratedDeriv 2 g`, so the continuity off the integers follows. -/
lemma contDiffAt_deriv_deriv_hurwitzKernel {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ}
    (hr : (r : UnitAddCircle) ≠ 0) : ContDiffAt ℝ ∞ (deriv (deriv (hurwitzKernel s))) r := by
  have h := contDiffAt_iteratedDeriv_two_hurwitzKernel hs0 hs1 hr
  have heq : iteratedDeriv 2 (hurwitzKernel s) = deriv (deriv (hurwitzKernel s)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [heq] at h
  exact h

/-- **Principal value of `Ψ g''` (non-integer endpoints).** For a `C²` coefficient `Ψ` with the
second-order cancellation at the integers, the truncated integrals converge to
`Ψ(b) g'(b) - Ψ(a) g'(a) - (Ψ'(b) g(b) - Ψ'(a) g(a) - ∫_a^b Ψ'' g)`. -/
theorem tendsto_truncated_by_parts_second {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ 2 Ψ) (hsec : ∃ M : ℝ, ∀ k : ℤ, ∀ δ : ℝ, 0 < δ → δ < 1 →
      |Ψ ((k : ℝ) + δ) + Ψ ((k : ℝ) - δ)| ≤ M * δ ^ 2)
    {a b : ℝ} (hab : a ≤ b) (ha : ∀ m : ℤ, a ≠ m) (hb : ∀ m : ℤ, b ≠ m) :
    Tendsto (fun δ : ℝ => ∫ v in a..b,
        (gradAllowed δ).indicator (fun v => Ψ v * deriv (deriv (hurwitzKernel s)) v) v) (𝓝[>] 0)
      (𝓝 (Ψ b * deriv (hurwitzKernel s) b - Ψ a * deriv (hurwitzKernel s) a
        - (deriv Ψ b * hurwitzKernel s b - deriv Ψ a * hurwitzKernel s a
          - ∫ v in a..b, deriv (deriv Ψ) v * hurwitzKernel s v))) := by
  obtain ⟨M, hM⟩ := hsec
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by norm_num)
  have hΨ2' : ContDiff ℝ (1 + 1) Ψ := by norm_num; exact hΨ
  have hΨ2 : ContDiff ℝ 1 (deriv Ψ) := ContDiff.deriv' hΨ2'
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 / 2 ∧ a ∈ gradAllowed δ ∧ b ∈ gradAllowed δ := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_mem_gradAllowed ha, eventually_mem_gradAllowed hb] with δ h1 h2 h3
    exact ⟨h1.1, h1.2, h2, h3⟩
  -- the truncated formula with kernel `g''` and antiderivative `g'`
  have hformula : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∫ v in a..b, (gradAllowed δ).indicator (fun v => Ψ v * deriv (deriv (hurwitzKernel s)) v) v
        = (Ψ b * deriv (hurwitzKernel s) b - Ψ a * deriv (hurwitzKernel s) a)
          + ∑ k ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
              (Ψ ((k : ℝ) - δ) * deriv (hurwitzKernel s) ((k : ℝ) - δ)
                - Ψ ((k : ℝ) + δ) * deriv (hurwitzKernel s) ((k : ℝ) + δ))
          - ∫ v in a..b, (gradAllowed δ).indicator (fun v => deriv Ψ v * deriv (hurwitzKernel s) v) v := by
    filter_upwards [hev] with δ ⟨hδ0, hδ1, ha', hb'⟩
    have hfl : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_mono hab
    have hn : ⌊b⌋ - ⌊a⌋ = (((⌊b⌋ - ⌊a⌋).toNat : ℕ) : ℤ) :=
      (Int.toNat_of_nonneg (by omega)).symm
    have hA : ∀ v ∈ gradAllowed δ, HasDerivAt (deriv (hurwitzKernel s))
        (deriv (deriv (hurwitzKernel s)) v) v := by
      intro v hv
      have hne := coe_ne_zero_of_mem_gradAllowed hδ0 hv
      exact ((contDiffAt_deriv_hurwitzKernel hs0 hs1 hne).differentiableAt (by simp)).hasDerivAt
    have hK : ContinuousOn (deriv (deriv (hurwitzKernel s))) (gradAllowed δ) := by
      intro v hv
      have hne := coe_ne_zero_of_mem_gradAllowed hδ0 hv
      exact (contDiffAt_deriv_deriv_hurwitzKernel hs0 hs1 hne).continuousAt.continuousWithinAt
    have hA' : ContinuousOn (deriv (hurwitzKernel s)) (gradAllowed δ) := by
      intro v hv
      have hne := coe_ne_zero_of_mem_gradAllowed hδ0 hv
      exact (contDiffAt_deriv_hurwitzKernel hs0 hs1 hne).continuousAt.continuousWithinAt
    exact gradTrunc_formula hδ0 hδ1 hΨ1 hA hK hA' _ a b hab ha' hb' hn
  -- the boundary sums vanish
  have hbsum : Tendsto (fun δ : ℝ => ∑ k ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
      (Ψ ((k : ℝ) - δ) * deriv (hurwitzKernel s) ((k : ℝ) - δ)
        - Ψ ((k : ℝ) + δ) * deriv (hurwitzKernel s) ((k : ℝ) + δ))) (𝓝[>] 0) (𝓝 0) := by
    have hbound : Tendsto (fun δ : ℝ => |M| * |δ ^ 2 * deriv (hurwitzKernel s) δ|) (𝓝[>] 0)
        (𝓝 0) := by
      have h := ((tendsto_sq_mul_deriv_hurwitzKernel_nhdsGT hs0 hs1).abs).const_mul |M|
      simpa using h
    have hterm : ∀ k ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Tendsto (fun δ : ℝ =>
        Ψ ((k : ℝ) - δ) * deriv (hurwitzKernel s) ((k : ℝ) - δ)
          - Ψ ((k : ℝ) + δ) * deriv (hurwitzKernel s) ((k : ℝ) + δ)) (𝓝[>] 0) (𝓝 0) := by
      intro k _
      refine squeeze_zero_norm' ?_ hbound
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
      have hδ0 : 0 < δ := hδ.1
      have hδ1 : δ < 1 := hδ.2
      rw [deriv_hurwitzKernel_int_sub s δ k, deriv_hurwitzKernel_int_add s δ k]
      have heq : Ψ ((k : ℝ) - δ) * -deriv (hurwitzKernel s) δ
          - Ψ ((k : ℝ) + δ) * deriv (hurwitzKernel s) δ
          = -deriv (hurwitzKernel s) δ * (Ψ ((k : ℝ) + δ) + Ψ ((k : ℝ) - δ)) := by ring
      rw [heq, Real.norm_eq_abs, abs_mul, abs_neg]
      have hs := hM k δ hδ0 hδ1
      calc |deriv (hurwitzKernel s) δ| * |Ψ ((k : ℝ) + δ) + Ψ ((k : ℝ) - δ)|
          ≤ |deriv (hurwitzKernel s) δ| * (M * δ ^ 2) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
        _ ≤ |deriv (hurwitzKernel s) δ| * (|M| * δ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
              (abs_nonneg _)
        _ = |M| * |δ ^ 2 * deriv (hurwitzKernel s) δ| := by
            rw [abs_mul, abs_of_pos (pow_pos hδ0 2)]; ring
    have hsum := tendsto_finsetSum (Finset.Ioc ⌊a⌋ ⌊b⌋) hterm
    simpa using hsum
  -- the remaining integral is a principal value
  have hJ := tendsto_truncated_by_parts hs0 hs1 hΨ2 hab ha (fun m => hb m)
  have hlim : Tendsto (fun δ : ℝ => (Ψ b * deriv (hurwitzKernel s) b - Ψ a * deriv (hurwitzKernel s) a)
      + ∑ k ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (Ψ ((k : ℝ) - δ) * deriv (hurwitzKernel s) ((k : ℝ) - δ)
          - Ψ ((k : ℝ) + δ) * deriv (hurwitzKernel s) ((k : ℝ) + δ))
        - ∫ v in a..b, (gradAllowed δ).indicator (fun v => deriv Ψ v * deriv (hurwitzKernel s) v) v)
      (𝓝[>] 0) (𝓝 ((Ψ b * deriv (hurwitzKernel s) b - Ψ a * deriv (hurwitzKernel s) a) + 0
        - (deriv Ψ b * hurwitzKernel s b - deriv Ψ a * hurwitzKernel s a
          - ∫ v in a..b, deriv (deriv Ψ) v * hurwitzKernel s v))) :=
    ((tendsto_const_nhds.add hbsum)).sub hJ
  rw [add_zero] at hlim
  exact (hlim.congr' (hformula.mono fun δ h => h.symm))

/-- **Principal value of `Ψ g''` with possibly integer endpoints.** The coefficient `Ψ` vanishes near
an integer endpoint (as the coefficient of `Z h'` does, see `GradientSplittingWindowPVEnds`). -/
theorem tendsto_truncated_by_parts_second_gen {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ 2 Ψ) (hsec : ∃ M : ℝ, ∀ k : ℤ, ∀ δ : ℝ, 0 < δ → δ < 1 →
      |Ψ ((k : ℝ) + δ) + Ψ ((k : ℝ) - δ)| ≤ M * δ ^ 2)
    {a b : ℝ} (hab : a < b) (ha : (∃ m : ℤ, a = m) → ∀ᶠ v in 𝓝 a, Ψ v = 0)
    (hb : (∃ m : ℤ, b = m) → ∀ᶠ v in 𝓝 b, Ψ v = 0) :
    Tendsto (fun δ : ℝ => ∫ v in a..b,
        (gradAllowed δ).indicator (fun v => Ψ v * deriv (deriv (hurwitzKernel s)) v) v) (𝓝[>] 0)
      (𝓝 (Ψ b * deriv (hurwitzKernel s) b - Ψ a * deriv (hurwitzKernel s) a
        - (deriv Ψ b * hurwitzKernel s b - deriv Ψ a * hurwitzKernel s a
          - ∫ v in a..b, deriv (deriv Ψ) v * hurwitzKernel s v))) := by
  obtain ⟨a', ha1, ha2, ha3, ha4⟩ := exists_shrink_left hab ha
  obtain ⟨b', hb1, hb2, hb3, hb4⟩ := exists_shrink_right hab hb
  have hab' : a' < b' := by linarith
  have hmain := tendsto_truncated_by_parts_second hs0 hs1 hΨ hsec hab'.le ha3 hb3
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by norm_num)
  have hΨ2' : ContDiff ℝ (1 + 1) Ψ := by norm_num; exact hΨ
  have hΨ2 : ContDiff ℝ 1 (deriv Ψ) := ContDiff.deriv' hΨ2'
  -- boundary values agree
  have hZa : Ψ a' * deriv (hurwitzKernel s) a' = Ψ a * deriv (hurwitzKernel s) a := by
    rcases ha4 with h | h
    · rw [h]
    · rw [(h a ⟨le_rfl, ha1⟩).1, (h a' ⟨ha1, le_rfl⟩).1]; ring
  have hZb : Ψ b' * deriv (hurwitzKernel s) b' = Ψ b * deriv (hurwitzKernel s) b := by
    rcases hb4 with h | h
    · rw [h]
    · rw [(h b ⟨hb2, le_rfl⟩).1, (h b' ⟨le_rfl, hb2⟩).1]; ring
  have hPa : deriv Ψ a' * hurwitzKernel s a' = deriv Ψ a * hurwitzKernel s a := by
    rcases ha4 with h | h
    · rw [h]
    · rw [(h a ⟨le_rfl, ha1⟩).2.1, (h a' ⟨ha1, le_rfl⟩).2.1]; ring
  have hPb : deriv Ψ b' * hurwitzKernel s b' = deriv Ψ b * hurwitzKernel s b := by
    rcases hb4 with h | h
    · rw [h]
    · rw [(h b ⟨hb2, le_rfl⟩).2.1, (h b' ⟨le_rfl, hb2⟩).2.1]; ring
  -- the integrals of `Ψ''g` agree
  have hint2 : IntervalIntegrable (fun v => deriv (deriv Ψ) v * hurwitzKernel s v) volume a b :=
    (hurwitzKernel_intervalIntegrable_all hs0 hs1 a b).continuousOn_mul
      (hΨ2.continuous_deriv le_rfl).continuousOn
  have hdd : ∫ v in a..b, deriv (deriv Ψ) v * hurwitzKernel s v
      = ∫ v in a'..b', deriv (deriv Ψ) v * hurwitzKernel s v :=
    integral_eq_of_zero_pieces hint2 ha1 hab'.le hb2
      (ha4.imp_right fun h v hv => by simp [(h v hv).2.2])
      (hb4.imp_right fun h v hv => by simp [(h v hv).2.2])
  -- the truncated integrals agree for every δ > 0
  have hF : ∀ δ : ℝ, 0 < δ → ∫ v in a..b,
      (gradAllowed δ).indicator (fun v => Ψ v * deriv (deriv (hurwitzKernel s)) v) v
        = ∫ v in a'..b', (gradAllowed δ).indicator
            (fun v => Ψ v * deriv (deriv (hurwitzKernel s)) v) v := by
    intro δ hδ
    have hGc : ContinuousOn (deriv (deriv (hurwitzKernel s))) (gradAllowed δ) := fun v hv =>
      (contDiffAt_deriv_deriv_hurwitzKernel hs0 hs1 (coe_ne_zero_of_mem_gradAllowed hδ hv)).continuousAt
        |>.continuousWithinAt
    have hcont : ContinuousOn (fun v => Ψ v * deriv (deriv (hurwitzKernel s)) v) (gradAllowed δ) :=
      hΨ.continuous.continuousOn.mul hGc
    have hI := intervalIntegrable_indicator_of_continuousOn (gradAllowed_isClosed δ) hcont a b
    exact integral_eq_of_zero_pieces hI ha1 hab'.le hb2
      (ha4.imp_right fun h v hv => by simp [(h v hv).1])
      (hb4.imp_right fun h v hv => by simp [(h v hv).1])
  have hint : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∫ v in a'..b',
      (gradAllowed δ).indicator (fun v => Ψ v * deriv (deriv (hurwitzKernel s)) v) v
        = ∫ v in a..b, (gradAllowed δ).indicator
            (fun v => Ψ v * deriv (deriv (hurwitzKernel s)) v) v := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hF δ hδ).symm
  have hvalue : Ψ b' * deriv (hurwitzKernel s) b' - Ψ a' * deriv (hurwitzKernel s) a'
      - (deriv Ψ b' * hurwitzKernel s b' - deriv Ψ a' * hurwitzKernel s a'
          - ∫ v in a'..b', deriv (deriv Ψ) v * hurwitzKernel s v)
      = Ψ b * deriv (hurwitzKernel s) b - Ψ a * deriv (hurwitzKernel s) a
        - (deriv Ψ b * hurwitzKernel s b - deriv Ψ a * hurwitzKernel s a
          - ∫ v in a..b, deriv (deriv Ψ) v * hurwitzKernel s v) := by
    rw [hZb, hZa, hPb, hPa, hdd]
  rw [← hvalue]
  exact hmain.congr' hint

end

end Riesz1
