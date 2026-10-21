/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowPV

/-!
# Principal value of `Φ g'` by truncated integration by parts

Let `g = hurwitzKernel s` and `G = deriv g`. For a `C¹` coefficient `Φ` and `a ≤ b` not integers,
the principal value of `∫_a^b Φ G` exists and equals `Φ(b) g(b) - Φ(a) g(a) - ∫_a^b Φ' g`
(`tendsto_truncated_by_parts`). The truncated integrals are those of `gradTrunc_formula`. Their
boundary sums vanish in the limit, because `g(k ± δ) = g(δ)` and `δ g(δ) → 0`, and the last
integral converges by dominated convergence, since `Φ' g` is interval integrable.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- A point off the integers is in the allowed set for all small `δ > 0`. -/
lemma eventually_mem_gradAllowed {v : ℝ} (hv : ∀ m : ℤ, v ≠ m) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), v ∈ gradAllowed δ := by
  set ε : ℝ := min (v - ⌊v⌋) (⌊v⌋ + 1 - v) with hε
  have hfl : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
  have hfl' : v < ⌊v⌋ + 1 := Int.lt_floor_add_one v
  have hne : v - ⌊v⌋ ≠ 0 := fun h => hv ⌊v⌋ (by linarith)
  have hεpos : 0 < ε := by
    have h1 : 0 < v - ⌊v⌋ := lt_of_le_of_ne (by linarith) (Ne.symm hne)
    have h2 : 0 < (⌊v⌋ : ℝ) + 1 - v := by linarith
    exact lt_min h1 h2
  filter_upwards [Ioo_mem_nhdsGT hεpos] with δ hδ
  intro m
  rcases le_or_gt m ⌊v⌋ with h | h
  · have hm : (m : ℝ) ≤ ⌊v⌋ := by exact_mod_cast h
    have h1 : |v - m| = v - m := abs_of_nonneg (by linarith)
    rw [h1]
    have : ε ≤ v - ⌊v⌋ := min_le_left _ _
    linarith [hδ.2]
  · have hm : (⌊v⌋ : ℝ) + 1 ≤ m := by exact_mod_cast h
    have h1 : |v - m| = -(v - m) := abs_of_nonpos (by linarith)
    rw [h1]
    have : ε ≤ ⌊v⌋ + 1 - v := min_le_right _ _
    linarith [hδ.2]

/-- Points of the allowed set for `δ > 0` are not integers. -/
lemma coe_ne_zero_of_mem_gradAllowed {δ v : ℝ} (hδ : 0 < δ) (hv : v ∈ gradAllowed δ) :
    (v : UnitAddCircle) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  rw [zsmul_eq_mul, mul_one] at hn
  have := hv n
  rw [← hn, sub_self, abs_zero] at this
  linarith

/-- The kernel is even. -/
lemma hurwitzKernel_neg' (s x : ℝ) : hurwitzKernel s (-x) = hurwitzKernel s x := by
  unfold hurwitzKernel
  rw [AddCircle.coe_neg, HurwitzZeta.hurwitzZetaEven_neg]

/-- The kernel is one-periodic, in the form `g(x + k) = g(x)` for integers `k`. -/
lemma hurwitzKernel_add_int (s x : ℝ) (k : ℤ) : hurwitzKernel s (x + k) = hurwitzKernel s x := by
  simpa using (hurwitzKernel_periodic s).int_mul k x

/-- `g(k - δ) = g(δ)` for an integer `k`. -/
lemma hurwitzKernel_int_sub (s δ : ℝ) (k : ℤ) :
    hurwitzKernel s ((k : ℝ) - δ) = hurwitzKernel s δ := by
  rw [show (k : ℝ) - δ = -δ + k by ring, hurwitzKernel_add_int, hurwitzKernel_neg']

/-- `g(k + δ) = g(δ)` for an integer `k`. -/
lemma hurwitzKernel_int_add (s δ : ℝ) (k : ℤ) :
    hurwitzKernel s ((k : ℝ) + δ) = hurwitzKernel s δ := by
  rw [show (k : ℝ) + δ = δ + k by ring, hurwitzKernel_add_int]

/-- The kernel is interval integrable on every interval, by periodicity. -/
lemma hurwitzKernel_intervalIntegrable_all {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (a b : ℝ) :
    IntervalIntegrable (hurwitzKernel s) volume a b := by
  have h01 : IntervalIntegrable (hurwitzKernel s) volume 0 (0 + 1) := by
    rw [zero_add]
    exact intervalIntegrable_hurwitzKernel s hs0 hs1
  exact (hurwitzKernel_periodic s).intervalIntegrable one_ne_zero h01 a b

/-- `δ g(δ) → 0` as `δ ↓ 0`, since `|g(δ)| ≤ C δ^{-s}` (kernel bound). -/
lemma tendsto_mul_hurwitzKernel_nhdsGT {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun δ : ℝ => δ * hurwitzKernel s δ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := gradSplit_iteratedDeriv_kernel_le s hs0 hs1 0
  have hlim : Tendsto (fun δ : ℝ => C * δ ^ (1 - s)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun δ : ℝ => δ ^ (1 - s)) (𝓝 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const (0 : ℝ) (1 - s) (Or.inr (by linarith))).tendsto
      rwa [Real.zero_rpow (by linarith : (0 : ℝ) < 1 - s).ne'] at h
    simpa using ((hc.const_mul C).mono_left nhdsWithin_le_nhds)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 3 / 4)] with δ hδ
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : |δ| ≤ 3 / 4 := by rw [abs_of_pos hδ0]; exact hδ.2.le
  have h := hb δ (by rw [abs_of_pos hδ0]; exact hδ0) hδ1
  simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, abs_of_pos hδ0] at h
  have hrp : δ ^ (1 - s) = δ * δ ^ (-s) := by
    rw [show 1 - s = 1 + (-s) by ring, Real.rpow_add hδ0, Real.rpow_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hδ0, hrp]
  calc δ * |hurwitzKernel s δ| ≤ δ * (C * δ ^ (-s)) := mul_le_mul_of_nonneg_left h hδ0.le
    _ = C * (δ * δ ^ (-s)) := by ring

/-- A Lipschitz bound for a `C¹` function on a compact interval, with a nonnegative constant. -/
lemma lipschitz_on_Icc {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (p q : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ Icc p q, ∀ w ∈ Icc p q, |Φ u - Φ w| ≤ L * |u - w| := by
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := p) (b := q)).exists_bound_of_continuousOn
    (hΦ.continuous_deriv le_rfl).continuousOn
  refine ⟨max L 0, le_max_right _ _, fun u hu w hw => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Φ) (s := Icc p q) (x := w) (y := u)
    (C := max L 0) (fun x _ => (hΦ.differentiable one_ne_zero) x)
    (fun x hx => (hL x hx).trans (le_max_left _ _)) (convex_Icc p q) hw hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- The boundary sums of the truncated formula vanish in the limit `δ ↓ 0`. -/
lemma tendsto_boundary_sum {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    (a b : ℝ) :
    Tendsto (fun δ : ℝ => ∑ k ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
      (Φ ((k : ℝ) - δ) * hurwitzKernel s ((k : ℝ) - δ)
        - Φ ((k : ℝ) + δ) * hurwitzKernel s ((k : ℝ) + δ))) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L, hL0, hL⟩ := lipschitz_on_Icc hΦ (a - 1) (b + 1)
  have hfl : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have hfl' : a < ⌊a⌋ + 1 := Int.lt_floor_add_one a
  have hfb : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  have hbound : Tendsto (fun δ : ℝ => 2 * L * |δ * hurwitzKernel s δ|) (𝓝[>] 0) (𝓝 0) := by
    have h := ((tendsto_mul_hurwitzKernel_nhdsGT hs0 hs1).abs).const_mul (2 * L)
    simpa using h
  have hterm : ∀ k ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Tendsto (fun δ : ℝ =>
      Φ ((k : ℝ) - δ) * hurwitzKernel s ((k : ℝ) - δ)
        - Φ ((k : ℝ) + δ) * hurwitzKernel s ((k : ℝ) + δ)) (𝓝[>] 0) (𝓝 0) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hk1 : (⌊a⌋ : ℝ) + 1 ≤ k := by exact_mod_cast (show ⌊a⌋ + 1 ≤ k by omega)
    have hk2 : (k : ℝ) ≤ ⌊b⌋ := by exact_mod_cast hk.2
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
    have hδ0 : 0 < δ := hδ.1
    have hδ1 : δ < 1 := hδ.2
    rw [hurwitzKernel_int_sub s δ k, hurwitzKernel_int_add s δ k]
    have hm1 : (k : ℝ) - δ ∈ Icc (a - 1) (b + 1) := ⟨by linarith, by linarith⟩
    have hm2 : (k : ℝ) + δ ∈ Icc (a - 1) (b + 1) := ⟨by linarith, by linarith⟩
    have hLip := hL _ hm1 _ hm2
    have hd : |(k : ℝ) - δ - ((k : ℝ) + δ)| = 2 * δ := by
      rw [show (k : ℝ) - δ - ((k : ℝ) + δ) = -(2 * δ) by ring, abs_neg,
        abs_of_pos (by linarith)]
    rw [hd] at hLip
    have heq : Φ ((k : ℝ) - δ) * hurwitzKernel s δ - Φ ((k : ℝ) + δ) * hurwitzKernel s δ
        = hurwitzKernel s δ * (Φ ((k : ℝ) - δ) - Φ ((k : ℝ) + δ)) := by ring
    rw [heq, Real.norm_eq_abs, abs_mul]
    calc |hurwitzKernel s δ| * |Φ ((k : ℝ) - δ) - Φ ((k : ℝ) + δ)|
        ≤ |hurwitzKernel s δ| * (L * (2 * δ)) := mul_le_mul_of_nonneg_left hLip (abs_nonneg _)
      _ = 2 * L * |δ * hurwitzKernel s δ| := by
        rw [abs_mul, abs_of_pos hδ0]; ring
  have hsum := tendsto_finsetSum (Finset.Ioc ⌊a⌋ ⌊b⌋) hterm
  simpa using hsum

/-- Dominated convergence for the allowed-set integral of `Φ' g`: its limit is the ordinary integral,
which exists because `g` is interval integrable. -/
lemma tendsto_indicator_deriv_mul {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {Φ : ℝ → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun δ : ℝ => ∫ v in a..b,
        (gradAllowed δ).indicator (fun v => deriv Φ v * hurwitzKernel s v) v) (𝓝[>] 0)
      (𝓝 (∫ v in a..b, deriv Φ v * hurwitzKernel s v)) := by
  have hcont : ∀ δ : ℝ, 0 < δ → ContinuousOn (fun v => deriv Φ v * hurwitzKernel s v)
      (gradAllowed δ) := by
    intro δ hδ v hv
    have hne := coe_ne_zero_of_mem_gradAllowed hδ hv
    have hg : ContinuousAt (hurwitzKernel s) v :=
      ((gradSplit_contDiffOn_kernel s hs0 hs1).contDiffAt
        (gradSplit_isOpen_nonInt.mem_nhds hne)).continuousAt
    exact ((hΦ.continuous_deriv le_rfl).continuousAt.mul hg).continuousWithinAt
  have hint : IntervalIntegrable (fun v => deriv Φ v * hurwitzKernel s v) volume a b :=
    (hurwitzKernel_intervalIntegrable_all hs0 hs1 a b).continuousOn_mul
      (hΦ.continuous_deriv le_rfl).continuousOn
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun v => |deriv Φ v * hurwitzKernel s v|) ?_ ?_ hint.abs ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hI := intervalIntegrable_indicator_of_continuousOn (gradAllowed_isClosed δ)
      (hcont δ hδ) a b
    rw [uIoc_of_le hab]
    exact hI.1.aestronglyMeasurable
  · refine Eventually.of_forall fun δ' => ae_of_all volume fun v => fun _ => ?_
    exact (norm_indicator_le_norm_self _ _).trans (le_of_eq (Real.norm_eq_abs _))
  · have hnull : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ Set.range (Int.cast : ℤ → ℝ) :=
      (Set.countable_range _).ae_notMem volume
    filter_upwards [hnull] with v hv _
    have hv' : ∀ m : ℤ, v ≠ m := fun m h => hv ⟨m, h.symm⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_gradAllowed hv'] with δ hδ
    exact (indicator_of_mem hδ (fun w => deriv Φ w * hurwitzKernel s w)).symm

/-- **Principal value of `Φ g'`.** For a `C¹` coefficient `Φ` and non-integers `a ≤ b`, the truncated
integrals over the allowed set converge as `δ ↓ 0` to `Φ(b) g(b) - Φ(a) g(a) - ∫_a^b Φ' g`. -/
theorem tendsto_truncated_by_parts {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {Φ : ℝ → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) {a b : ℝ} (hab : a ≤ b) (ha : ∀ m : ℤ, a ≠ m) (hb : ∀ m : ℤ, b ≠ m) :
    Tendsto (fun δ : ℝ => ∫ v in a..b,
        (gradAllowed δ).indicator (fun v => Φ v * deriv (hurwitzKernel s) v) v) (𝓝[>] 0)
      (𝓝 (Φ b * hurwitzKernel s b - Φ a * hurwitzKernel s a
        - ∫ v in a..b, deriv Φ v * hurwitzKernel s v)) := by
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 / 2 ∧ a ∈ gradAllowed δ ∧ b ∈ gradAllowed δ := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_mem_gradAllowed ha, eventually_mem_gradAllowed hb] with δ h1 h2 h3
    exact ⟨h1.1, h1.2, h2, h3⟩
  have hformula : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∫ v in a..b, (gradAllowed δ).indicator (fun v => Φ v * deriv (hurwitzKernel s) v) v
        = (Φ b * hurwitzKernel s b - Φ a * hurwitzKernel s a)
          + ∑ k ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
              (Φ ((k : ℝ) - δ) * hurwitzKernel s ((k : ℝ) - δ)
                - Φ ((k : ℝ) + δ) * hurwitzKernel s ((k : ℝ) + δ))
          - ∫ v in a..b, (gradAllowed δ).indicator (fun v => deriv Φ v * hurwitzKernel s v) v := by
    filter_upwards [hev] with δ ⟨hδ0, hδ1, ha', hb'⟩
    have hfl : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_mono hab
    have hn : ⌊b⌋ - ⌊a⌋ = (((⌊b⌋ - ⌊a⌋).toNat : ℕ) : ℤ) :=
      (Int.toNat_of_nonneg (by omega)).symm
    have hA : ∀ v ∈ gradAllowed δ, HasDerivAt (hurwitzKernel s) (deriv (hurwitzKernel s) v) v := by
      intro v hv
      have hne := coe_ne_zero_of_mem_gradAllowed hδ0 hv
      exact (((gradSplit_contDiffOn_kernel s hs0 hs1).contDiffAt
        (gradSplit_isOpen_nonInt.mem_nhds hne)).differentiableAt (by simp)).hasDerivAt
    have hK : ContinuousOn (deriv (hurwitzKernel s)) (gradAllowed δ) := by
      intro v hv
      have hne := coe_ne_zero_of_mem_gradAllowed hδ0 hv
      exact (contDiffAt_deriv_hurwitzKernel hs0 hs1 hne).continuousAt.continuousWithinAt
    have hA' : ContinuousOn (hurwitzKernel s) (gradAllowed δ) := by
      intro v hv
      have hne := coe_ne_zero_of_mem_gradAllowed hδ0 hv
      exact (((gradSplit_contDiffOn_kernel s hs0 hs1).contDiffAt
        (gradSplit_isOpen_nonInt.mem_nhds hne)).continuousAt).continuousWithinAt
    exact gradTrunc_formula hδ0 hδ1 hΦ hA hK hA' _ a b hab ha' hb' hn
  have hS := tendsto_boundary_sum hs0 hs1 hΦ a b
  have hJ := tendsto_indicator_deriv_mul hs0 hs1 hΦ hab
  have hlim : Tendsto (fun δ : ℝ => (Φ b * hurwitzKernel s b - Φ a * hurwitzKernel s a)
      + (∑ k ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
        (Φ ((k : ℝ) - δ) * hurwitzKernel s ((k : ℝ) - δ)
          - Φ ((k : ℝ) + δ) * hurwitzKernel s ((k : ℝ) + δ)))
        - ∫ v in a..b, (gradAllowed δ).indicator (fun v => deriv Φ v * hurwitzKernel s v) v)
      (𝓝[>] 0) (𝓝 ((Φ b * hurwitzKernel s b - Φ a * hurwitzKernel s a) + 0
        - ∫ v in a..b, deriv Φ v * hurwitzKernel s v)) :=
    (tendsto_const_nhds.add hS).sub hJ
  rw [add_zero] at hlim
  exact hlim.congr' (hformula.mono fun δ h => h.symm)

end

end Riesz1
