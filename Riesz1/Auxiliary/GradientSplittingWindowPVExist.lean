/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowBackground
public import Riesz1.Auxiliary.GradientSplittingWindowPVEnds
public import Riesz1.Auxiliary.GradientSplittingWindowPVSecond

/-!
# Existence and value of the two principal values of `V`

In the `v`-frame (`v = y - x`) the two principal values of the field `V` are
the limits of the truncated integrals of

* `Z_x(x,y) h(y-x) = (Z(x,y) - ψ'(x/ℓ)) G(v)`, with `G = deriv (hurwitzKernel s)`.
* `Z(x,y) h'(y-x) = Z(x,y) G(v) + D(v) G'(v)` off the integers, with `D(v) = ℓ(ψ((x+v)/ℓ) - ψ(x/ℓ))`.

Both limits exist (`tendsto_truncated_by_parts_gen`, `tendsto_truncated_by_parts_second_gen`), and
their difference is an explicit expression, which is `J'(x)` in the next file.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- If `D` vanishes near `a` and `ψ'(x/ℓ) = 0`, then `Z(x, x+·)` vanishes near `a`. -/
lemma gradZ_eventually_zero_of_gradD {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    {x a : ℝ} (hq : deriv ψ (x / ℓ) = 0) (hD : ∀ᶠ v in 𝓝 a, gradD ψ ℓ x v = 0) :
    ∀ᶠ v in 𝓝 a, gradZ ψ ℓ x (x + v) = 0 := by
  filter_upwards [hD] with v hv
  by_cases hv0 : v = 0
  · subst hv0
    simp [gradZ_self, hq]
  · have h := gradZ_mul_eq_gradD hψ hℓ x v
    rw [hv] at h
    exact (mul_eq_zero.1 h).resolve_right hv0

/-- The coefficient `q = ψ'(x/ℓ)` of the principal value times the truncated integral of `G` has
the expected limit: at an integer endpoint `q = 0`, and otherwise the truncated integral of `G`
converges. -/
lemma tendsto_q_mul_truncated_deriv {ψ : ℝ → ℝ} (_hψ : ContDiff ℝ ∞ ψ) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (q : ℝ) {a b : ℝ} (hab : a < b)
    (hqa : (∃ m : ℤ, a = m) → q = 0) (hqb : (∃ m : ℤ, b = m) → q = 0) :
    Tendsto (fun δ : ℝ => q * ∫ v in a..b, (gradAllowed δ).indicator (fun v => deriv (hurwitzKernel s) v) v)
      (𝓝[>] 0) (𝓝 (q * (hurwitzKernel s b - hurwitzKernel s a))) := by
  by_cases hint : (∃ m : ℤ, a = m) ∨ (∃ m : ℤ, b = m)
  · have hq : q = 0 := by
      rcases hint with h | h
      · exact hqa h
      · exact hqb h
    subst hq
    simp only [zero_mul]
    exact tendsto_const_nhds
  · simp only [not_or, not_exists] at hint
    obtain ⟨ha, hb⟩ := hint
    have hF := tendsto_truncated_by_parts hs0 hs1 (Φ := fun _ => (1 : ℝ))
      contDiff_const hab.le ha hb
    have hF' : Tendsto (fun δ : ℝ => ∫ v in a..b, (gradAllowed δ).indicator (fun v => deriv (hurwitzKernel s) v) v)
        (𝓝[>] 0) (𝓝 (hurwitzKernel s b - hurwitzKernel s a)) := by
      have := hF
      simp only [one_mul, deriv_const, zero_mul, intervalIntegral.integral_zero, sub_zero,
        one_mul] at this
      exact this
    exact hF'.const_mul q

/-- The two principal values of `V` in the `v`-frame: both limits exist, and their difference is the
explicit combination `-q(g(b)-g(a)) - [D G' terms]` (`q = ψ'(x/ℓ)`, `D = gradD`). -/
theorem gradV_pv_limits {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) {a b : ℝ}
    (hab : a < b) (ha : (∃ m : ℤ, a = m) → ∀ᶠ v in 𝓝 a, gradD ψ ℓ x v = 0)
    (hb : (∃ m : ℤ, b = m) → ∀ᶠ v in 𝓝 b, gradD ψ ℓ x v = 0)
    (hqa : (∃ m : ℤ, a = m) → deriv ψ (x / ℓ) = 0) (hqb : (∃ m : ℤ, b = m) → deriv ψ (x / ℓ) = 0) :
    ∃ LA LB : ℝ,
      Tendsto (fun δ : ℝ => ∫ v in a..b,
        (gradAllowed δ).indicator (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v) (𝓝[>] 0)
        (𝓝 LA) ∧
      Tendsto (fun δ : ℝ => ∫ v in a..b,
        (gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v) v)
        (𝓝[>] 0) (𝓝 LB) ∧
      LA - LB = -(deriv ψ (x / ℓ)) * (hurwitzKernel s b - hurwitzKernel s a)
        - (gradD ψ ℓ x b * deriv (hurwitzKernel s) b - gradD ψ ℓ x a * deriv (hurwitzKernel s) a
          - (deriv (gradD ψ ℓ x) b * hurwitzKernel s b - deriv (gradD ψ ℓ x) a * hurwitzKernel s a
            - ∫ v in a..b, deriv (deriv (gradD ψ ℓ x)) v * hurwitzKernel s v)) := by
  set q : ℝ := deriv ψ (x / ℓ) with hq
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hA1 : ContDiff ℝ 1 (fun v : ℝ => gradZ ψ ℓ x (x + v)) :=
    contDiff_one_gradZ_shift hψ hℓ.ne' x
  have hD2 : ContDiff ℝ 2 (gradD ψ ℓ x) := ((contDiff_gradD hψ ℓ x).of_le (by simp))
  -- the principal value of `Z G` (coefficient `Z(x,x+·)`)
  have hAG := tendsto_truncated_by_parts_gen hs0 hs1 (Φ := fun v : ℝ => gradZ ψ ℓ x (x + v))
    hA1 hab
    (fun h => gradZ_eventually_zero_of_gradD hψ hℓ.ne' (hqa h) (ha h))
    (fun h => gradZ_eventually_zero_of_gradD hψ hℓ.ne' (hqb h) (hb h))
  obtain ⟨LAG, hAG'⟩ : ∃ L, Tendsto (fun δ : ℝ => ∫ v in a..b,
      (gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v) v)
      (𝓝[>] 0) (𝓝 L) := ⟨_, hAG⟩
  -- the principal value of `D G''`
  obtain ⟨M, hM⟩ := second_diff_periodic_le (hψ.of_le (by simp)) hℓ hp x
  have hsec : ∃ M : ℝ, ∀ k : ℤ, ∀ δ : ℝ, 0 < δ → δ < 1 →
      |gradD ψ ℓ x ((k : ℝ) + δ) + gradD ψ ℓ x ((k : ℝ) - δ)| ≤ M * δ ^ 2 :=
    ⟨M, fun k δ h0 h1 => hM k δ h0 h1⟩
  have hDG := tendsto_truncated_by_parts_second_gen hs0 hs1 (Ψ := gradD ψ ℓ x) hD2 hsec hab ha hb
  -- continuity of the integrands on the allowed set
  have hGc : ∀ δ : ℝ, 0 < δ → ContinuousOn (fun v => deriv (hurwitzKernel s) v) (gradAllowed δ) :=
    fun δ hδ v hv => (contDiffAt_deriv_hurwitzKernel hs0 hs1
      (coe_ne_zero_of_mem_gradAllowed hδ hv)).continuousAt.continuousWithinAt
  have hAc : Continuous fun v : ℝ => gradZ ψ ℓ x (x + v) := hA1.continuous
  have hcontAG : ∀ δ : ℝ, 0 < δ → ContinuousOn
      (fun v => gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v) (gradAllowed δ) :=
    fun δ hδ => hAc.continuousOn.mul (hGc δ hδ)
  have hcontDG : ∀ δ : ℝ, 0 < δ → ContinuousOn
      (fun v => gradD ψ ℓ x v * deriv (deriv (hurwitzKernel s)) v) (gradAllowed δ) := by
    intro δ hδ v hv
    have hne := coe_ne_zero_of_mem_gradAllowed hδ hv
    exact ((contDiff_gradD hψ ℓ x).continuous.continuousAt.mul
      (contDiffAt_deriv_deriv_hurwitzKernel hs0 hs1 hne).continuousAt).continuousWithinAt
  have hintAG : ∀ δ : ℝ, 0 < δ → IntervalIntegrable
      ((gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v)) volume a b :=
    fun δ hδ => intervalIntegrable_indicator_of_continuousOn (gradAllowed_isClosed δ) (hcontAG δ hδ) a b
  have hintG : ∀ δ : ℝ, 0 < δ → IntervalIntegrable
      ((gradAllowed δ).indicator (fun v => deriv (hurwitzKernel s) v)) volume a b :=
    fun δ hδ => intervalIntegrable_indicator_of_continuousOn (gradAllowed_isClosed δ) (hGc δ hδ) a b
  have hintDG : ∀ δ : ℝ, 0 < δ → IntervalIntegrable
      ((gradAllowed δ).indicator (fun v => gradD ψ ℓ x v * deriv (deriv (hurwitzKernel s)) v)) volume a b :=
    fun δ hδ => intervalIntegrable_indicator_of_continuousOn (gradAllowed_isClosed δ) (hcontDG δ hδ) a b
  -- the first integrand: `Z_x h = (Z - q) G`
  have hI1 : ∀ δ : ℝ, 0 < δ →
      ∫ v in a..b, (gradAllowed δ).indicator (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v
        = (∫ v in a..b, (gradAllowed δ).indicator
            (fun v => gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v) v)
          - q * ∫ v in a..b, (gradAllowed δ).indicator (fun v => deriv (hurwitzKernel s) v) v := by
    intro δ hδ
    have hpt : ∀ v : ℝ, (gradAllowed δ).indicator (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v
        = (gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v) v
          - q * (gradAllowed δ).indicator (fun v => deriv (hurwitzKernel s) v) v := by
      intro v
      by_cases hv : v ∈ gradAllowed δ
      · rw [indicator_of_mem hv, indicator_of_mem hv, indicator_of_mem hv,
          gradZx_mul_kernelH_shift]
        ring
      · rw [indicator_of_notMem hv, indicator_of_notMem hv, indicator_of_notMem hv]
        ring
    rw [intervalIntegral.integral_congr (fun v _ => hpt v),
      intervalIntegral.integral_sub (hintAG δ hδ) ((hintG δ hδ).const_mul q),
      intervalIntegral.integral_const_mul]
  -- the second integrand: `Z h' = Z G + D G''` off the integers
  have hI2 : ∀ δ : ℝ, 0 < δ →
      ∫ v in a..b, (gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v) v
        = (∫ v in a..b, (gradAllowed δ).indicator
            (fun v => gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v) v)
          + ∫ v in a..b, (gradAllowed δ).indicator
            (fun v => gradD ψ ℓ x v * deriv (deriv (hurwitzKernel s)) v) v := by
    intro δ hδ
    have hpt : ∀ v : ℝ, (gradAllowed δ).indicator
        (fun v => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v) v
        = (gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v) v
          + (gradAllowed δ).indicator (fun v => gradD ψ ℓ x v * deriv (deriv (hurwitzKernel s)) v) v := by
      intro v
      by_cases hv : v ∈ gradAllowed δ
      · rw [indicator_of_mem hv, indicator_of_mem hv, indicator_of_mem hv]
        exact gradZ_mul_deriv_kernelH hψ hℓ.ne' hs0 hs1 x v (coe_ne_zero_of_mem_gradAllowed hδ hv)
      · rw [indicator_of_notMem hv, indicator_of_notMem hv, indicator_of_notMem hv]
        ring
    rw [intervalIntegral.integral_congr (fun v _ => hpt v),
      intervalIntegral.integral_add (hintAG δ hδ) (hintDG δ hδ)]
  -- the limits
  have hqlim := tendsto_q_mul_truncated_deriv hψ hs0 hs1 q hab hqa hqb
  have hLA : Tendsto (fun δ : ℝ => ∫ v in a..b,
      (gradAllowed δ).indicator (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v) (𝓝[>] 0)
      (𝓝 (LAG - q * (hurwitzKernel s b - hurwitzKernel s a))) := by
    refine (hAG'.sub hqlim).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hI1 δ hδ).symm
  have hI2ev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∫ v in a..b, (gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v) v
        = (∫ v in a..b, (gradAllowed δ).indicator
            (fun v => gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v) v)
          + ∫ v in a..b, (gradAllowed δ).indicator
            (fun v => gradD ψ ℓ x v * deriv (deriv (hurwitzKernel s)) v) v := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hI2 δ hδ
  have hI1ev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∫ v in a..b, (gradAllowed δ).indicator (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v
        = (∫ v in a..b, (gradAllowed δ).indicator
            (fun v => gradZ ψ ℓ x (x + v) * deriv (hurwitzKernel s) v) v)
          - q * ∫ v in a..b, (gradAllowed δ).indicator (fun v => deriv (hurwitzKernel s) v) v := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hI1 δ hδ
  have hLA := (hAG'.sub hqlim).congr' (hI1ev.mono fun δ h => h.symm)
  have hLB := (hAG'.add hDG).congr' (hI2ev.mono fun δ h => h.symm)
  refine ⟨_, _, hLA, hLB, ?_⟩
  ring

end

end Riesz1
