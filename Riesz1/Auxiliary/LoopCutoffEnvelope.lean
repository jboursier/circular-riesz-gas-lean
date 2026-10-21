/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffDefs
public import Riesz1.Auxiliary.GradientSplittingZArc
public import Riesz1.Auxiliary.GradientSplittingZWeights
public import Riesz1.Auxiliary.GradientSplittingZBounds
public import Riesz1.Auxiliary.GradientSplittingDifferences

/-!
# Derivative envelopes of the localized transport

The cutoff part of Lemma 5.8, the envelope clause: if `ψ` satisfies
`|ψ'| ≤ C₀ w₁` and `|ψ''| ≤ C₀ w₂` on the circle `ℓ^{-1}𝕋`, then the transport `ψ_γ` of
`loopTransport` satisfies the same two envelopes with a constant depending only on `s`, `α` and
the cutoff `χ`.

This file proves the principal-domain estimates. On `|u| ≤ (2ℓ)^{-1}` the transport is
`χ(u/R) (ψ(u) - ψ((2ℓ)^{-1}))` with `R = τ/ℓ = K^{γ-1} ≥ 1`. The derivative of the cutoff is
supported where `|u| ∈ [R/8, R/4]`. Two regimes cover this support: `R ≥ 8`, where `|u| ≥ 1`, and
`1 ≤ R < 8`, where `|u| ∈ [1/8, 2]` and the weights are bounded above and below.

The envelope on the whole circle is `loopTransport_envelope`, which combines these estimates with
the periodicity of `loopTransport` and the shift `r = t + m ℓ^{-1}` onto `[-(2ℓ)^{-1}, (2ℓ)^{-1})`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace Riesz1

noncomputable section

/-! ## The cutoff `χ` -/

/-- The derivatives of a smooth compactly supported function are bounded. -/
lemma cutoff_deriv_bounds {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ M1 M2 : ℝ, ∀ x : ℝ, |deriv χ x| ≤ M1 ∧ |deriv (deriv χ) x| ≤ M2 := by
  have hd1 : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv χ)) := (contDiff_infty_iff_deriv.mp hd1).2
  have hc1 : HasCompactSupport (deriv χ) := hχc.deriv
  have hc2 : HasCompactSupport (deriv (deriv χ)) := hc1.deriv
  obtain ⟨M1, hM1⟩ := hd1.continuous.bounded_above_of_compact_support hc1
  obtain ⟨M2, hM2⟩ := hd2.continuous.bounded_above_of_compact_support hc2
  refine ⟨M1, M2, fun x => ⟨?_, ?_⟩⟩
  · rw [← Real.norm_eq_abs]
    exact hM1 x
  · rw [← Real.norm_eq_abs]
    exact hM2 x

/-- The cutoff is constant on `(-1/8, 1/8)` and vanishes off `(-1/4, 1/4)`, so its first two
derivatives vanish off `[-1/4, -1/8] ∪ [1/8, 1/4]`. -/
lemma cutoff_deriv_zero {χ : ℝ → ℝ} (hχ1 : ∀ x : ℝ, |x| < 1 / 8 → χ x = 1)
    (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4)) (x : ℝ) (hx : |x| < 1 / 8 ∨ 1 / 4 < |x|) :
    deriv χ x = 0 ∧ deriv (deriv χ) x = 0 := by
  rcases hx with hx | hx
  · have hopen : IsOpen {y : ℝ | |y| < 1 / 8} := isOpen_lt continuous_abs continuous_const
    have hev : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => hχ1 y hy
    have hd : deriv χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hev.deriv] with y hy
      rw [hy, deriv_const]
    exact ⟨by rw [hev.deriv_eq, deriv_const], by rw [hd.deriv_eq, deriv_const]⟩
  · have hx' : x ∉ tsupport χ := by
      intro h
      have hin := abs_lt.mpr (hχs h)
      linarith
    refine ⟨deriv_of_notMem_tsupport hx', deriv_of_notMem_tsupport ?_⟩
    exact fun h => hx' (tsupport_deriv_subset h)

/-! ## The weights on the principal domain -/

/-- On the principal domain, `|u| ≤ L/2`, the circular distance is `|u|`. -/
lemma circDist_abs_of_le {L u : ℝ} (hL : 0 < L) (hu : |u| ≤ L / 2) :
    circDist L u = |u| := by
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu ⊢
    exact circDist_of_mem_Icc hL h hu
  · rw [abs_of_nonpos h] at hu ⊢
    have := circDist_neg_of_mem_Icc hL (t := -u) (by linarith) (by linarith)
    rwa [neg_neg] at this

/-- The weight `w₂` on `[1, L/2]` is `t^{s-3}`. -/
lemma gradWeightTwo_eq_rpow_of_abs {s a K L u : ℝ} (hL : 0 < L) (hu1 : 1 ≤ |u|) (hu : |u| ≤ L / 2) :
    gradWeightTwo s a K L u = |u| ^ (s - 3) := by
  rw [gradWeightTwo_eq_of_one_le (by rw [circDist_abs_of_le hL hu]; exact hu1),
    circDist_abs_of_le hL hu]

/-- The weight `w₁` on `[1, L/2]` is `|u|^{s-2}`. -/
lemma gradWeightOne_eq_rpow_of_abs {s a K L u : ℝ} (hL : 0 < L) (hu1 : 1 ≤ |u|) (hu : |u| ≤ L / 2) :
    gradWeightOne s a K L u = |u| ^ (s - 2) := by
  rw [gradWeightOne_of_one_le (by rw [circDist_abs_of_le hL hu]; exact hu1),
    circDist_abs_of_le hL hu]

/-- On `1/8 ≤ |u| ≤ 2`, the weight `w₁` lies between `2^{s-2}` and `8^a`. -/
lemma gradWeightOne_bounds_mid {s a K L u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (hK : 1 ≤ K) (hL : 0 < L) (hu0 : 1 / 8 ≤ |u|) (hu2 : |u| ≤ 2) (hu : |u| ≤ L / 2) :
    2 ^ (s - 2) ≤ gradWeightOne s a K L u ∧ gradWeightOne s a K L u ≤ 8 ^ a := by
  rcases lt_or_ge |u| 1 with h1 | h1
  · have hm := gradWeightOne_eq_max (s := s) (a := a) (K := K) (L := L) (t := |u|) hL hK
      (abs_nonneg u) (by linarith) hu
    have hu' : gradWeightOne s a K L u = gradWeightOne s a K L |u| := by
      rcases le_total 0 u with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, gradWeightOne_neg hL]
    rw [hu', hm]
    have hK0 : 0 < K⁻¹ := inv_pos.mpr (by linarith)
    have hmax1 : max |u| K⁻¹ ≤ 1 := max_le (by linarith) (inv_le_one_of_one_le₀ hK)
    have hmax0 : 1 / 8 ≤ max |u| K⁻¹ := le_trans hu0 (le_max_left _ _)
    constructor
    · have : (1 : ℝ) ≤ max |u| K⁻¹ ^ (-a) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) hmax1 (by linarith)
      have h2 : (2 : ℝ) ^ (s - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      linarith
    · have : max |u| K⁻¹ ^ (-a) ≤ (1 / 8) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hmax0 (by linarith)
      have e : ((1 : ℝ) / 8) ^ (-a) = 8 ^ a := by
        rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]
      linarith
  · rw [gradWeightOne_eq_rpow_of_abs hL h1 hu]
    have hpos : 0 < |u| := by linarith
    constructor
    · exact Real.rpow_le_rpow_of_nonpos hpos hu2 (by linarith)
    · have h1' : |u| ^ (s - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
      have h8 : (1 : ℝ) ≤ 8 ^ a := Real.one_le_rpow (by norm_num) ha0
      linarith

/-- On `1/8 ≤ |u| ≤ 2`, the weight `w₂` is at least `2^{s-3}`. -/
lemma gradWeightTwo_lower_mid {s a K L u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a)
    (hK : 1 ≤ K) (hL : 0 < L) (_hu0 : 1 / 8 ≤ |u|) (hu2 : |u| ≤ 2) (hu : |u| ≤ L / 2) :
    2 ^ (s - 3) ≤ gradWeightTwo s a K L u := by
  rcases lt_or_ge |u| 1 with h1 | h1
  · have hu' : gradWeightTwo s a K L u = gradWeightTwo s a K L |u| := by
      rcases le_total 0 u with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, gradWeightTwo_neg hL]
    rw [hu']
    have hK0 : 0 < K⁻¹ := inv_pos.mpr (by linarith)
    have hcirc : circDist L |u| = |u| := by
      rw [circDist_abs_of_le hL (by rw [abs_abs]; exact hu), abs_abs]
    have hw : gradWeightTwo s a K L |u| = max |u| K⁻¹ ^ (-(1 + a)) := by
      unfold gradWeightTwo
      simp only [hcirc, h1, ↓reduceIte]
    rw [hw]
    have hmax1 : max |u| K⁻¹ ≤ 1 := max_le (by linarith) (inv_le_one_of_one_le₀ hK)
    have : (1 : ℝ) ≤ max |u| K⁻¹ ^ (-(1 + a)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (lt_max_of_lt_right hK0) hmax1 (by linarith)
    have h2 : (2 : ℝ) ^ (s - 3) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    linarith
  · rw [gradWeightTwo_eq_rpow_of_abs hL h1 hu]
    have hpos : 0 < |u| := by linarith
    exact Real.rpow_le_rpow_of_nonpos hpos hu2 (by linarith)

/-- The integral of `w₁` from `r` to `L/2` is at most `(1 + 1/(1-a)) + 1/(1-s)`. -/
lemma integral_gradWeightOne_tail_le {s a K L r : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha1 : a < 1) (hK : 1 ≤ K) (hL : 0 < L) (hr0 : 0 ≤ r) (hrL : r ≤ L / 2) :
    ∫ t in r..(L / 2), gradWeightOne s a K L t ≤ (1 + 1 / (1 - a)) + 1 / (1 - s) := by
  have hL2 : 0 ≤ L / 2 := by linarith
  have hint : IntervalIntegrable (fun t => gradWeightOne s a K L t) volume 0 (L / 2) :=
    intervalIntegrable_gradWeightOne hL hK hL2 le_rfl
  have hsub1 : uIcc (0 : ℝ) r ⊆ uIcc 0 (L / 2) :=
    uIcc_subset_uIcc (Set.left_mem_uIcc) (Set.mem_uIcc.mpr (Or.inl ⟨hr0, hrL⟩))
  have hsub2 : uIcc r (L / 2) ⊆ uIcc 0 (L / 2) :=
    uIcc_subset_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨hr0, hrL⟩)) Set.right_mem_uIcc
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set hsub1) (hint.mono_set hsub2)
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..r, gradWeightOne s a K L t :=
    intervalIntegral.integral_nonneg hr0 (fun t _ => gradWeightOne_nonneg hK)
  have hW := gradWeightOneIntegral_le_const hL ha1 hs0 hs1 hK hL2 le_rfl
  unfold gradWeightOneIntegral at hW
  linarith

/-- The tail integral of `w₁` from `r ≥ 1` to `L/2` is at most `r^{s-1}/(1-s)`. -/
lemma integral_gradWeightOne_tail_le_rpow {s a K L r : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hL : 0 < L) (hr1 : 1 ≤ r) (hrL : r ≤ L / 2) :
    ∫ t in r..(L / 2), gradWeightOne s a K L t ≤ r ^ (s - 1) / (1 - s) := by
  have heq : ∫ t in r..(L / 2), gradWeightOne s a K L t = ∫ t in r..(L / 2), t ^ (s - 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hrL] at ht
    exact gradWeightOne_eq_rpow hL (by linarith [ht.1]) ht.2
  rw [heq]
  exact integral_rpow_sub_two_le hs0 hs1 hr1 hrL

/-! ## The difference `ψ(u) - ψ(L/2)` -/

/-- For `0 ≤ u ≤ L/2`, `|ψ(L/2) - ψ(u)| ≤ C₀ ∫_u^{L/2} w₁`. -/
lemma psi_sub_half_le_of_nonneg {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {s a K L C0 u : ℝ}
    (hK : 1 ≤ K) (hL : 0 < L) (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t)
    (hu0 : 0 ≤ u) (huL : u ≤ L / 2) :
    |ψ (L / 2) - ψ u| ≤ C0 * ∫ t in u..(L / 2), gradWeightOne s a K L t := by
  have hdiff : ∀ t, HasDerivAt ψ (deriv ψ t) t := fun t =>
    ((hψ.differentiable (by simp)) t).hasDerivAt
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hFTC : ∫ t in u..(L / 2), deriv ψ t = ψ (L / 2) - ψ u :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hdiff t)
      (hcont.intervalIntegrable _ _)
  have hint : IntervalIntegrable (fun t => gradWeightOne s a K L t) volume u (L / 2) := by
    apply IntervalIntegrable.mono_set (intervalIntegrable_gradWeightOne hL hK (by linarith) le_rfl)
    exact uIcc_subset_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨hu0, huL⟩)) Set.right_mem_uIcc
  have hnorm : ‖∫ t in u..(L / 2), deriv ψ t‖ ≤ ∫ t in u..(L / 2), C0 * gradWeightOne s a K L t :=
    intervalIntegral.norm_integral_le_of_norm_le huL
      (ae_of_all _ fun t _ => by rw [Real.norm_eq_abs]; exact hbd t) (hint.const_mul C0)
  have habs : |ψ (L / 2) - ψ u| = ‖∫ t in u..(L / 2), deriv ψ t‖ := by
    rw [hFTC, Real.norm_eq_abs]
  rw [habs]
  exact hnorm.trans_eq (intervalIntegral.integral_const_mul _ _)

/-- For `|u| ≤ L/2`, `|ψ(L/2) - ψ(u)| ≤ C₀ ∫_{|u|}^{L/2} w₁`, using the periodicity of `ψ` for
`u < 0`. -/
lemma psi_sub_half_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {s a K L C0 u : ℝ} (hK : 1 ≤ K)
    (hL : 0 < L) (hper : Function.Periodic ψ L)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t) (hu : |u| ≤ L / 2) :
    |ψ (L / 2) - ψ u| ≤ C0 * ∫ t in |u|..(L / 2), gradWeightOne s a K L t := by
  rcases le_total 0 u with h0 | h0
  · rw [abs_of_nonneg h0] at hu ⊢
    exact psi_sub_half_le_of_nonneg hψ hK hL hbd h0 hu
  · rw [abs_of_nonpos h0] at hu ⊢
    -- Reflect: `φ(t) = ψ(-t)` satisfies the envelope on `[0, L/2]`.
    set φ : ℝ → ℝ := fun t => ψ (-t) with hφdef
    have hφ : ContDiff ℝ ∞ φ := hψ.comp contDiff_neg
    have hφd : ∀ t, deriv φ t = -deriv ψ (-t) := by
      intro t
      rw [hφdef, deriv_comp_neg]
    have hφbd : ∀ t, |deriv φ t| ≤ C0 * gradWeightOne s a K L t := by
      intro t
      rw [hφd, abs_neg]
      have := hbd (-t)
      rwa [gradWeightOne_neg hL t] at this
    have hpeq : ψ (L / 2) = ψ (-(L / 2)) := by
      have := hper (-(L / 2))
      rw [show -(L / 2) + L = L / 2 by ring] at this
      exact this
    have h1 := psi_sub_half_le_of_nonneg hφ hK hL hφbd (u := -u) (by linarith) (by linarith)
    have hφL : φ (L / 2) = ψ (-(L / 2)) := by simp [hφdef]
    have hφu : φ (-u) = ψ u := by simp [hφdef]
    rw [hφL, hφu, ← hpeq] at h1
    exact h1

/-! ## The principal-domain profile and its derivatives -/

/-- The profile `v ↦ χ(v/R) (ψ(v) - c)`, whose derivatives are the principal-domain formulas of the
transport: `ψ_γ = G(rep u)` with `G = loopProfile χ ψ (τ/ℓ) (ψ((2ℓ)^{-1}))`. -/
def loopProfile (χ ψ : ℝ → ℝ) (R c v : ℝ) : ℝ := χ (v / R) * (ψ v - c)

/-- The first derivative of `loopProfile`. -/
def loopProfileD1 (χ ψ : ℝ → ℝ) (R c v : ℝ) : ℝ :=
  (1 / R) * deriv χ (v / R) * (ψ v - c) + χ (v / R) * deriv ψ v

/-- The second derivative of `loopProfile`. -/
def loopProfileD2 (χ ψ : ℝ → ℝ) (R c v : ℝ) : ℝ :=
  (1 / R) * ((1 / R) * deriv (deriv χ) (v / R)) * (ψ v - c) +
    2 * ((1 / R) * deriv χ (v / R)) * deriv ψ v + χ (v / R) * deriv (deriv ψ) v

/-- The chain rule for `x ↦ f(x/R)`. -/
lemma hasDerivAt_comp_div {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {R : ℝ} (_hR : R ≠ 0) (v : ℝ) :
    HasDerivAt (fun x => f (x / R)) ((1 / R) * deriv f (v / R)) v := by
  have h1 : HasDerivAt (fun x : ℝ => x / R) (1 / R) v := (hasDerivAt_id v).div_const R
  have h2 : HasDerivAt f (deriv f (v / R)) (v / R) :=
    ((hf.differentiable (by simp)) (v / R)).hasDerivAt
  exact (h2.comp v h1).congr_deriv (by ring)

/-- The derivative of `loopProfile`. -/
lemma hasDerivAt_loopProfile {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    {R c : ℝ} (hR : R ≠ 0) (v : ℝ) :
    HasDerivAt (loopProfile χ ψ R c) (loopProfileD1 χ ψ R c v) v := by
  have h1 := hasDerivAt_comp_div hχ hR v
  have h2 : HasDerivAt (fun x => ψ x - c) (deriv ψ v) v :=
    ((hψ.differentiable (by simp)) v).hasDerivAt.sub_const c
  exact (h1.mul h2).congr_deriv (by unfold loopProfileD1; ring)

/-- The derivative of `loopProfileD1`. -/
lemma hasDerivAt_loopProfileD1 {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    {R c : ℝ} (hR : R ≠ 0) (v : ℝ) :
    HasDerivAt (loopProfileD1 χ ψ R c) (loopProfileD2 χ ψ R c v) v := by
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hψ' : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hA : HasDerivAt (fun x => (1 / R) * deriv χ (x / R))
      ((1 / R) * ((1 / R) * deriv (deriv χ) (v / R))) v :=
    (hasDerivAt_comp_div hχ' hR v).const_mul (1 / R)
  have hψc : HasDerivAt (fun x => ψ x - c) (deriv ψ v) v :=
    ((hψ.differentiable (by simp)) v).hasDerivAt.sub_const c
  have hψd : HasDerivAt (deriv ψ) (deriv (deriv ψ) v) v :=
    ((hψ'.differentiable (by simp)) v).hasDerivAt
  have hB : HasDerivAt (fun x => χ (x / R) * deriv ψ x)
      ((1 / R) * deriv χ (v / R) * deriv ψ v + χ (v / R) * deriv (deriv ψ) v) v :=
    (hasDerivAt_comp_div hχ hR v).mul hψd
  have hC := (hA.mul hψc).add hB
  exact hC.congr_deriv (by unfold loopProfileD2; ring)

/-- The first derivative of `loopProfile` is `loopProfileD1`, as a function. -/
lemma deriv_loopProfile {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    {R c : ℝ} (hR : R ≠ 0) :
    deriv (loopProfile χ ψ R c) = loopProfileD1 χ ψ R c := by
  funext v
  exact (hasDerivAt_loopProfile hχ hψ hR v).deriv

/-- The second derivative of `loopProfile` is `loopProfileD2`. -/
lemma deriv_deriv_loopProfile {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    {R c : ℝ} (hR : R ≠ 0) (v : ℝ) :
    deriv (deriv (loopProfile χ ψ R c)) v = loopProfileD2 χ ψ R c v := by
  rw [deriv_loopProfile hχ hψ hR]
  exact (hasDerivAt_loopProfileD1 hχ hψ hR v).deriv

/-! ## Bounds on the principal-domain derivatives -/

/-- Where a derivative of the cutoff is nonzero, `|v|/R ∈ [1/8, 1/4]`. -/
lemma support_of_deriv {χ : ℝ → ℝ} (hχ1 : ∀ x : ℝ, |x| < 1 / 8 → χ x = 1)
    (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4)) {R v : ℝ} (hR : 0 < R)
    (hd : deriv χ (v / R) ≠ 0 ∨ deriv (deriv χ) (v / R) ≠ 0) :
    1 / 8 ≤ |v| / R ∧ |v| / R ≤ 1 / 4 := by
  have habs : |v / R| = |v| / R := by rw [abs_div, abs_of_pos hR]
  by_contra hc
  have hz : deriv χ (v / R) = 0 ∧ deriv (deriv χ) (v / R) = 0 := by
    rcases lt_or_ge (|v| / R) (1 / 8) with h1 | h1
    · exact cutoff_deriv_zero hχ1 hχs (v / R) (Or.inl (by rw [habs]; exact h1))
    · have h2 : 1 / 4 < |v| / R := by
        by_contra h2'
        exact hc ⟨h1, not_lt.mp h2'⟩
      exact cutoff_deriv_zero hχ1 hχs (v / R) (Or.inr (by rw [habs]; exact h2))
  rcases hd with hd | hd
  · exact hd hz.1
  · exact hd hz.2

/-- The first-derivative envelope on the principal domain, with `W₀` the constant of
`integral_gradWeightOne_tail_le`. -/
lemma loopProfileD1_bound {χ ψ : ℝ → ℝ} (hχ1 : ∀ x : ℝ, |x| < 1 / 8 → χ x = 1)
    (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4)) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {M1 : ℝ} (hM1 : ∀ x, |deriv χ x| ≤ M1) (hM1nn : 0 ≤ M1)
    {s a K L C0 c R v : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hK : 1 ≤ K) (hL : 0 < L) (hR : 1 ≤ R) (hC0 : 0 ≤ C0) (hv : |v| ≤ L / 2)
    (hψd : |ψ v - c| ≤ C0 * ∫ t in |v|..(L / 2), gradWeightOne s a K L t)
    (hψ' : |deriv ψ v| ≤ C0 * gradWeightOne s a K L v) :
    |loopProfileD1 χ ψ R c v| ≤
      (1 + M1 * (1 / (4 * (1 - s)) + ((1 + 1 / (1 - a)) + 1 / (1 - s)) * 2 ^ (2 - s))) *
        C0 * gradWeightOne s a K L v := by
  have hR0 : 0 < R := by linarith
  have hw0 : 0 ≤ gradWeightOne s a K L v := gradWeightOne_nonneg hK
  have ht0 : 0 ≤ |v| := abs_nonneg v
  have ha1' : 0 ≤ 1 - a := by linarith
  have hs1' : 0 < 1 - s := by linarith
  have hW0nn : 0 ≤ (1 + 1 / (1 - a)) + 1 / (1 - s) := by
    have := div_nonneg zero_le_one ha1'
    have := div_nonneg zero_le_one hs1'.le
    linarith
  set W0 : ℝ := (1 + 1 / (1 - a)) + 1 / (1 - s) with hW0def
  set w : ℝ := gradWeightOne s a K L v with hwdef
  set t : ℝ := |v| with htdef
  set p : ℝ := 1 / R with hpdef
  have hp0 : 0 < p := div_pos one_pos hR0
  have hp1 : p ≤ 1 := by rw [hpdef, div_le_one hR0]; exact hR
  have hpt : p * t = t / R := by rw [hpdef]; ring
  have hv' : t ≤ L / 2 := hv
  have hψ0 : |ψ v - c| ≤ C0 * W0 := by
    refine hψd.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact integral_gradWeightOne_tail_le hs0 hs1 ha1 hK hL ht0 hv'
  set K1 : ℝ := M1 * (1 / (4 * (1 - s)) + W0 * 2 ^ (2 - s)) with hK1def
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]
    refine mul_nonneg hM1nn (add_nonneg (div_nonneg zero_le_one (by linarith)) ?_)
    exact mul_nonneg hW0nn (Real.rpow_nonneg (by norm_num) _)
  -- The second term.
  have hT2 : |χ (v / R) * deriv ψ v| ≤ C0 * w := by
    rw [abs_mul]
    have hχa : |χ (v / R)| ≤ 1 := by
      rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
    calc |χ (v / R)| * |deriv ψ v| ≤ 1 * |deriv ψ v| :=
          mul_le_mul_of_nonneg_right hχa (abs_nonneg _)
      _ ≤ C0 * w := by rw [one_mul]; exact hψ'
  -- The first term.
  have hT1 : |p * deriv χ (v / R) * (ψ v - c)| ≤ K1 * (C0 * w) := by
    rw [abs_mul, abs_mul, abs_of_pos hp0]
    by_cases hχ' : deriv χ (v / R) = 0
    · rw [hχ', abs_zero, mul_zero, zero_mul]
      exact mul_nonneg hK1nn (mul_nonneg hC0 hw0)
    have hsupp := support_of_deriv hχ1 hχs hR0 (Or.inl hχ')
    rw [← hpt] at hsupp
    have hpt1 : 1 / 8 ≤ p * t := hsupp.1
    have hpt2 : p * t ≤ 1 / 4 := hsupp.2
    rcases le_or_gt p (1 / 8) with hp8 | hp8
    · -- The regime `R ≥ 8`: here `|v| ≥ 1` and the weight is a power.
      have ht1 : 1 ≤ t := by
        have : p * t ≤ 1 / 8 * t := mul_le_mul_of_nonneg_right hp8 ht0
        linarith
      have hw : w = t ^ (s - 2) := gradWeightOne_eq_rpow_of_abs hL ht1 hv'
      have hpsi : |ψ v - c| ≤ C0 * (t ^ (s - 1) / (1 - s)) := by
        refine hψd.trans (mul_le_mul_of_nonneg_left ?_ hC0)
        exact integral_gradWeightOne_tail_le_rpow hs0 hs1 hL ht1 hv'
      have hts : t ^ (s - 1) = t ^ (s - 2) * t := by
        have h := Real.rpow_add_one (ne_of_gt (lt_of_lt_of_le one_pos ht1)) (s - 2)
        rw [show s - 2 + 1 = s - 1 by ring] at h
        exact h
      have hχM : |deriv χ (v / R)| ≤ M1 := hM1 _
      calc p * |deriv χ (v / R)| * |ψ v - c|
          ≤ p * M1 * (C0 * (t ^ (s - 1) / (1 - s))) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hχM hp0.le) hpsi (abs_nonneg _)
            exact mul_nonneg hp0.le hM1nn
        _ = (M1 * C0 * t ^ (s - 2) / (1 - s)) * (p * t) := by rw [hts]; ring
        _ ≤ (M1 * C0 * t ^ (s - 2) / (1 - s)) * (1 / 4) := by
            apply mul_le_mul_of_nonneg_left hpt2
            apply div_nonneg (mul_nonneg (mul_nonneg hM1nn hC0) (Real.rpow_nonneg (by linarith) _))
              hs1'.le
        _ ≤ K1 * (C0 * w) := by
            rw [hw, hK1def]
            have hx : 0 ≤ C0 * t ^ (s - 2) := mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _)
            have e : (M1 * C0 * t ^ (s - 2) / (1 - s)) * (1 / 4) =
                M1 * (1 / (4 * (1 - s))) * (C0 * t ^ (s - 2)) := by
              field_simp
            rw [e]
            have hextra : 0 ≤ M1 * (W0 * 2 ^ (2 - s)) * (C0 * t ^ (s - 2)) := by
              apply mul_nonneg (mul_nonneg hM1nn (mul_nonneg hW0nn (Real.rpow_nonneg (by norm_num) _)))
              exact hx
            have e2 : M1 * (1 / (4 * (1 - s)) + W0 * 2 ^ (2 - s)) * (C0 * t ^ (s - 2)) =
                M1 * (1 / (4 * (1 - s))) * (C0 * t ^ (s - 2)) +
                  M1 * (W0 * 2 ^ (2 - s)) * (C0 * t ^ (s - 2)) := by ring
            rw [e2]
            linarith [hextra]
    · -- The regime `1 ≤ R < 8`: here `|v| ∈ [1/8, 2]`, so the weight is bounded below.
      have ht1 : 1 / 8 ≤ t := by
        have : p * t ≤ 1 * t := mul_le_mul_of_nonneg_right hp1 ht0
        linarith
      have ht2 : t ≤ 2 := by
        have : 1 / 8 * t ≤ p * t := mul_le_mul_of_nonneg_right hp8.le ht0
        linarith
      have hlo := (gradWeightOne_bounds_mid (K := K) hs0 hs1 ha0 hK hL ht1 ht2 hv').1
      have hχM : |deriv χ (v / R)| ≤ M1 := hM1 _
      have hone : (1 : ℝ) ≤ 2 ^ (2 - s) * w := by
        have e : (2 : ℝ) ^ (2 - s) * 2 ^ (s - 2) = 1 := by
          rw [← Real.rpow_add (by norm_num)]
          norm_num
        calc (1 : ℝ) = 2 ^ (2 - s) * 2 ^ (s - 2) := e.symm
          _ ≤ 2 ^ (2 - s) * w := mul_le_mul_of_nonneg_left hlo (Real.rpow_nonneg (by norm_num) _)
      calc p * |deriv χ (v / R)| * |ψ v - c|
          ≤ 1 * M1 * (C0 * W0) := by
            apply mul_le_mul (mul_le_mul hp1 hχM (abs_nonneg _) zero_le_one) hψ0 (abs_nonneg _)
            exact mul_nonneg zero_le_one hM1nn
        _ ≤ (M1 * W0 * 2 ^ (2 - s)) * (C0 * w) := by
            have hA : 0 ≤ M1 * W0 * C0 := mul_nonneg (mul_nonneg hM1nn hW0nn) hC0
            calc 1 * M1 * (C0 * W0) = (M1 * W0 * C0) * 1 := by ring
              _ ≤ (M1 * W0 * C0) * (2 ^ (2 - s) * w) := mul_le_mul_of_nonneg_left hone hA
              _ = (M1 * W0 * 2 ^ (2 - s)) * (C0 * w) := by ring
        _ ≤ K1 * (C0 * w) := by
            have h1 : 0 ≤ M1 * (1 / (4 * (1 - s))) :=
              mul_nonneg hM1nn (div_nonneg zero_le_one (by linarith))
            have hK1ge : M1 * W0 * 2 ^ (2 - s) ≤ K1 := by
              rw [hK1def]
              calc M1 * W0 * 2 ^ (2 - s) ≤ M1 * (1 / (4 * (1 - s))) + M1 * W0 * 2 ^ (2 - s) :=
                    le_add_of_nonneg_left h1
                _ = M1 * (1 / (4 * (1 - s)) + W0 * 2 ^ (2 - s)) := by ring
            exact mul_le_mul_of_nonneg_right hK1ge (mul_nonneg hC0 hw0)
  calc |loopProfileD1 χ ψ R c v| = |p * deriv χ (v / R) * (ψ v - c) + χ (v / R) * deriv ψ v| := rfl
    _ ≤ |p * deriv χ (v / R) * (ψ v - c)| + |χ (v / R) * deriv ψ v| := abs_add_le _ _
    _ ≤ K1 * (C0 * w) + C0 * w := add_le_add hT1 hT2
    _ = (1 + M1 * (1 / (4 * (1 - s)) + W0 * 2 ^ (2 - s))) * C0 * w := by rw [hK1def]; ring

/-- The power identities of the weights at `t = |v| ≥ 1`: `t^{s-2} = t^{s-3} t` and
`t^{s-1} = t^{s-3} t²`. -/
lemma rpow_shift_identities {s t : ℝ} (ht1 : 1 ≤ t) :
    t ^ (s - 2) = t ^ (s - 3) * t ∧ t ^ (s - 1) = t ^ (s - 3) * t * t := by
  have ht : t ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos ht1)
  have h1 : t ^ (s - 3 + 1) = t ^ (s - 3) * t := Real.rpow_add_one ht (s - 3)
  have h2 : t ^ (s - 2 + 1) = t ^ (s - 2) * t := Real.rpow_add_one ht (s - 2)
  rw [show s - 3 + 1 = s - 2 by ring] at h1
  rw [show s - 2 + 1 = s - 1 by ring] at h2
  exact ⟨h1, by rw [h2, h1]⟩

/-- The mixed term `2 (p χ'(v/R)) ψ'(v)` of the second derivative, with `p = 1/R`. -/
lemma mixed_term_bound {χ ψ : ℝ → ℝ} (hχ1 : ∀ x : ℝ, |x| < 1 / 8 → χ x = 1)
    (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4))
    {M1 : ℝ} (hM1 : ∀ x, |deriv χ x| ≤ M1) (hM1nn : 0 ≤ M1)
    {s a K L C0 R v : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (_ha1 : a < 1)
    (hK : 1 ≤ K) (hL : 0 < L) (hR : 1 ≤ R) (hC0 : 0 ≤ C0) (hv : |v| ≤ L / 2)
    (hψ' : |deriv ψ v| ≤ C0 * gradWeightOne s a K L v) :
    |2 * ((1 / R) * deriv χ (v / R)) * deriv ψ v| ≤
      M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s)) * (C0 * gradWeightTwo s a K L v) := by
  have hR0 : 0 < R := by linarith
  have hw2 : 0 ≤ gradWeightTwo s a K L v := gradWeightTwo_nonneg hK
  have ht0 : 0 ≤ |v| := abs_nonneg v
  have h8a : (0 : ℝ) ≤ 8 ^ a := Real.rpow_nonneg (by norm_num) _
  have h23 : (0 : ℝ) ≤ 2 ^ (3 - s) := Real.rpow_nonneg (by norm_num) _
  have hKb0 : 0 ≤ M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s)) := by
    refine mul_nonneg hM1nn (add_nonneg (by norm_num) ?_)
    exact mul_nonneg (mul_nonneg (by norm_num) h8a) h23
  set w1 : ℝ := gradWeightOne s a K L v with hw1def
  set w2 : ℝ := gradWeightTwo s a K L v with hw2def
  set t : ℝ := |v| with htdef
  set p : ℝ := 1 / R with hpdef
  have hp0 : 0 < p := div_pos one_pos hR0
  have hp1 : p ≤ 1 := by rw [hpdef, div_le_one hR0]; exact hR
  have hpt : p * t = t / R := by rw [hpdef]; ring
  have habs : |2 * (p * deriv χ (v / R)) * deriv ψ v| =
      2 * (p * |deriv χ (v / R)|) * |deriv ψ v| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hp0, abs_two]
  have hmain : 2 * ((1 / R) * deriv χ (v / R)) * deriv ψ v =
      2 * (p * deriv χ (v / R)) * deriv ψ v := rfl
  rw [hmain, habs]
  by_cases hχ' : deriv χ (v / R) = 0
  · rw [hχ', abs_zero, mul_zero, mul_zero, zero_mul]
    exact mul_nonneg hKb0 (mul_nonneg hC0 hw2)
  have hsupp := support_of_deriv hχ1 hχs hR0 (Or.inl hχ')
  rw [← hpt] at hsupp
  have hpt2 : p * t ≤ 1 / 4 := hsupp.2
  have hpt1 : 1 / 8 ≤ p * t := hsupp.1
  have hχM : |deriv χ (v / R)| ≤ M1 := hM1 _
  rcases le_or_gt p (1 / 8) with hp8 | hp8
  · -- The regime `R ≥ 8`: `|v| ≥ 1`, and `w₂ = t^{s-3}`.
    have ht1 : 1 ≤ t := by
      have : p * t ≤ 1 / 8 * t := mul_le_mul_of_nonneg_right hp8 ht0
      linarith
    obtain ⟨hA, -⟩ := rpow_shift_identities (s := s) ht1
    have hw1eq : w1 = t ^ (s - 2) := gradWeightOne_eq_rpow_of_abs hL ht1 hv
    have hw2eq : w2 = t ^ (s - 3) := gradWeightTwo_eq_rpow_of_abs hL (by linarith) hv
    have hpM : p * |deriv χ (v / R)| ≤ p * M1 := mul_le_mul_of_nonneg_left hχM hp0.le
    have hstep : 2 * (p * |deriv χ (v / R)|) * |deriv ψ v| ≤ 2 * (p * M1) * (C0 * w1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpM (by norm_num)) hψ' (abs_nonneg _)
        (by positivity)
    calc 2 * (p * |deriv χ (v / R)|) * |deriv ψ v| ≤ 2 * (p * M1) * (C0 * w1) := hstep
      _ = (2 * M1 * C0 * t ^ (s - 3)) * (p * t) := by rw [hw1eq, hA]; ring
      _ ≤ (2 * M1 * C0 * t ^ (s - 3)) * (1 / 4) := by
          refine mul_le_mul_of_nonneg_left hpt2 ?_
          exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM1nn) hC0)
            (Real.rpow_nonneg (by linarith) _)
      _ = (M1 / 2) * (C0 * w2) := by rw [hw2eq]; ring
      _ ≤ M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s)) * (C0 * w2) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC0 hw2)
          have h0 : 0 ≤ M1 * (2 * 8 ^ a * 2 ^ (3 - s)) :=
            mul_nonneg hM1nn (mul_nonneg (mul_nonneg (by norm_num) h8a) h23)
          have e : M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s)) =
              M1 / 2 + M1 * (2 * 8 ^ a * 2 ^ (3 - s)) := by ring
          rw [e]
          exact le_add_of_nonneg_right h0
  · -- The regime `1 ≤ R < 8`: `|v| ∈ [1/8, 2]`, so `w₁ ≤ 8^a` and `w₂ ≥ 2^{s-3}`.
    have ht1 : 1 / 8 ≤ t := by
      have : p * t ≤ 1 * t := mul_le_mul_of_nonneg_right hp1 ht0
      linarith
    have ht2 : t ≤ 2 := by
      have : 1 / 8 * t ≤ p * t := mul_le_mul_of_nonneg_right hp8.le ht0
      linarith
    have hw1le : w1 ≤ 8 ^ a := (gradWeightOne_bounds_mid hs0 hs1 ha0 hK hL ht1 ht2 hv).2
    have hlo2 := gradWeightTwo_lower_mid hs0 hs1 ha0 hK hL ht1 ht2 hv
    have hone : (1 : ℝ) ≤ 2 ^ (3 - s) * w2 := by
      have e : (2 : ℝ) ^ (3 - s) * 2 ^ (s - 3) = 1 := by
        rw [← Real.rpow_add (by norm_num)]
        norm_num
      calc (1 : ℝ) = 2 ^ (3 - s) * 2 ^ (s - 3) := e.symm
        _ ≤ 2 ^ (3 - s) * w2 := mul_le_mul_of_nonneg_left hlo2 h23
    have hpM : p * |deriv χ (v / R)| ≤ 1 * M1 := mul_le_mul hp1 hχM (abs_nonneg _) zero_le_one
    have hstep : 2 * (p * |deriv χ (v / R)|) * |deriv ψ v| ≤ 2 * (1 * M1) * (C0 * w1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpM (by norm_num)) hψ' (abs_nonneg _)
        (by positivity)
    have hA : 0 ≤ 2 * M1 * C0 * 8 ^ a := by positivity
    calc 2 * (p * |deriv χ (v / R)|) * |deriv ψ v| ≤ 2 * (1 * M1) * (C0 * w1) := hstep
      _ ≤ 2 * (1 * M1) * (C0 * 8 ^ a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw1le hC0) (by positivity)
      _ = (2 * M1 * C0 * 8 ^ a) * 1 := by ring
      _ ≤ (2 * M1 * C0 * 8 ^ a) * (2 ^ (3 - s) * w2) := mul_le_mul_of_nonneg_left hone hA
      _ = (2 * 8 ^ a * 2 ^ (3 - s)) * M1 * (C0 * w2) := by ring
      _ ≤ M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s)) * (C0 * w2) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC0 hw2)
          have h0 : 0 ≤ M1 * (1 / 2) := mul_nonneg hM1nn (by norm_num)
          have e : M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s)) =
              M1 * (1 / 2) + M1 * (2 * 8 ^ a * 2 ^ (3 - s)) := by ring
          rw [e]
          have e2 : (2 * 8 ^ a * 2 ^ (3 - s)) * M1 = M1 * (2 * 8 ^ a * 2 ^ (3 - s)) := by ring
          rw [e2]
          exact le_add_of_nonneg_left h0

/-- The diagonal term `p (p χ''(v/R)) (ψ(v) - c)` of the second derivative. -/
lemma diag_term_bound {χ ψ : ℝ → ℝ} (hχ1 : ∀ x : ℝ, |x| < 1 / 8 → χ x = 1)
    (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4))
    {M2 : ℝ} (hM2 : ∀ x, |deriv (deriv χ) x| ≤ M2) (hM2nn : 0 ≤ M2)
    {s a K L C0 c R v : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hK : 1 ≤ K) (hL : 0 < L) (hR : 1 ≤ R) (hC0 : 0 ≤ C0) (hv : |v| ≤ L / 2)
    (hψd : |ψ v - c| ≤ C0 * ∫ t in |v|..(L / 2), gradWeightOne s a K L t) :
    |(1 / R) * ((1 / R) * deriv (deriv χ) (v / R)) * (ψ v - c)| ≤
      M2 * (1 / (16 * (1 - s)) + ((1 + 1 / (1 - a)) + 1 / (1 - s)) * 2 ^ (3 - s)) *
        (C0 * gradWeightTwo s a K L v) := by
  have hR0 : 0 < R := by linarith
  have hw2 : 0 ≤ gradWeightTwo s a K L v := gradWeightTwo_nonneg hK
  have ht0 : 0 ≤ |v| := abs_nonneg v
  have ha1' : 0 ≤ 1 - a := by linarith
  have hs1' : 0 < 1 - s := by linarith
  have hW0nn : 0 ≤ (1 + 1 / (1 - a)) + 1 / (1 - s) := by
    have := div_nonneg zero_le_one ha1'
    have := div_nonneg zero_le_one hs1'.le
    linarith
  have h23 : (0 : ℝ) ≤ 2 ^ (3 - s) := Real.rpow_nonneg (by norm_num) _
  set W0 : ℝ := (1 + 1 / (1 - a)) + 1 / (1 - s) with hW0def
  set w2 : ℝ := gradWeightTwo s a K L v with hw2def
  set t : ℝ := |v| with htdef
  set p : ℝ := 1 / R with hpdef
  have hp0 : 0 < p := div_pos one_pos hR0
  have hp1 : p ≤ 1 := by rw [hpdef, div_le_one hR0]; exact hR
  have hpt : p * t = t / R := by rw [hpdef]; ring
  have hψ0 : |ψ v - c| ≤ C0 * W0 := by
    refine hψd.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact integral_gradWeightOne_tail_le hs0 hs1 ha1 hK hL ht0 hv
  have hKa0 : 0 ≤ M2 * (1 / (16 * (1 - s)) + W0 * 2 ^ (3 - s)) := by
    refine mul_nonneg hM2nn (add_nonneg (div_nonneg zero_le_one (by linarith)) ?_)
    exact mul_nonneg hW0nn h23
  have habs : |(1 / R) * ((1 / R) * deriv (deriv χ) (v / R)) * (ψ v - c)| =
      p * (p * |deriv (deriv χ) (v / R)|) * |ψ v - c| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hp0]
  rw [habs]
  by_cases hχ'' : deriv (deriv χ) (v / R) = 0
  · rw [hχ'', abs_zero, mul_zero, mul_zero, zero_mul]
    exact mul_nonneg hKa0 (mul_nonneg hC0 hw2)
  have hsupp := support_of_deriv hχ1 hχs hR0 (Or.inr hχ'')
  rw [← hpt] at hsupp
  have hpt2 : p * t ≤ 1 / 4 := hsupp.2
  have hpt0 : 0 ≤ p * t := mul_nonneg hp0.le ht0
  have hχM : |deriv (deriv χ) (v / R)| ≤ M2 := hM2 _
  have hpM : p * |deriv (deriv χ) (v / R)| ≤ p * M2 := mul_le_mul_of_nonneg_left hχM hp0.le
  rcases le_or_gt p (1 / 8) with hp8 | hp8
  · -- The regime `R ≥ 8`.
    have ht1 : 1 ≤ t := by
      have : p * t ≤ 1 / 8 * t := mul_le_mul_of_nonneg_right hp8 ht0
      have := hsupp.1
      linarith
    obtain ⟨-, hB⟩ := rpow_shift_identities (s := s) ht1
    have hw2eq : w2 = t ^ (s - 3) := gradWeightTwo_eq_rpow_of_abs hL (by linarith) hv
    have hpsi : |ψ v - c| ≤ C0 * (t ^ (s - 1) / (1 - s)) := by
      refine hψd.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      exact integral_gradWeightOne_tail_le_rpow hs0 hs1 hL ht1 hv
    calc p * (p * |deriv (deriv χ) (v / R)|) * |ψ v - c|
        ≤ p * (p * M2) * (C0 * (t ^ (s - 1) / (1 - s))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpM hp0.le) hpsi (abs_nonneg _)
            (by positivity)
      _ = (M2 * C0 * t ^ (s - 3) / (1 - s)) * ((p * t) * (p * t)) := by rw [hB]; ring
      _ ≤ (M2 * C0 * t ^ (s - 3) / (1 - s)) * (1 / 16) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · have := mul_le_mul hpt2 hpt2 hpt0 (by norm_num)
            linarith
          · exact div_nonneg (mul_nonneg (mul_nonneg hM2nn hC0) (Real.rpow_nonneg (by linarith) _))
              hs1'.le
      _ = (M2 / (16 * (1 - s))) * (C0 * w2) := by rw [hw2eq]; field_simp
      _ ≤ M2 * (1 / (16 * (1 - s)) + W0 * 2 ^ (3 - s)) * (C0 * w2) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC0 hw2)
          have h0 : 0 ≤ M2 * (W0 * 2 ^ (3 - s)) := mul_nonneg hM2nn (mul_nonneg hW0nn h23)
          have e : M2 * (1 / (16 * (1 - s)) + W0 * 2 ^ (3 - s)) =
              M2 * (1 / (16 * (1 - s))) + M2 * (W0 * 2 ^ (3 - s)) := by ring
          rw [e]
          have e2 : M2 / (16 * (1 - s)) = M2 * (1 / (16 * (1 - s))) := by ring
          rw [e2]
          exact le_add_of_nonneg_right h0
  · -- The regime `1 ≤ R < 8`.
    have ht1 : 1 / 8 ≤ t := by
      have : p * t ≤ 1 * t := mul_le_mul_of_nonneg_right hp1 ht0
      have := hsupp.1
      linarith
    have ht2 : t ≤ 2 := by
      have : 1 / 8 * t ≤ p * t := mul_le_mul_of_nonneg_right hp8.le ht0
      linarith
    have hlo2 := gradWeightTwo_lower_mid hs0 hs1 ha0 hK hL ht1 ht2 hv
    have hone : (1 : ℝ) ≤ 2 ^ (3 - s) * w2 := by
      have e : (2 : ℝ) ^ (3 - s) * 2 ^ (s - 3) = 1 := by
        rw [← Real.rpow_add (by norm_num)]
        norm_num
      calc (1 : ℝ) = 2 ^ (3 - s) * 2 ^ (s - 3) := e.symm
        _ ≤ 2 ^ (3 - s) * w2 := mul_le_mul_of_nonneg_left hlo2 h23
    have hpM1 : p * |deriv (deriv χ) (v / R)| ≤ 1 * M2 := mul_le_mul hp1 hχM (abs_nonneg _) zero_le_one
    have hA : 0 ≤ M2 * W0 * C0 := mul_nonneg (mul_nonneg hM2nn hW0nn) hC0
    calc p * (p * |deriv (deriv χ) (v / R)|) * |ψ v - c|
        ≤ 1 * (1 * M2) * (C0 * W0) := by
          refine mul_le_mul (mul_le_mul hp1 hpM1 (by positivity) zero_le_one) hψ0 (abs_nonneg _)
            (by positivity)
      _ = (M2 * W0 * C0) * 1 := by ring
      _ ≤ (M2 * W0 * C0) * (2 ^ (3 - s) * w2) := mul_le_mul_of_nonneg_left hone hA
      _ = (M2 * W0 * 2 ^ (3 - s)) * (C0 * w2) := by ring
      _ ≤ M2 * (1 / (16 * (1 - s)) + W0 * 2 ^ (3 - s)) * (C0 * w2) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC0 hw2)
          have h0 : 0 ≤ M2 * (1 / (16 * (1 - s))) :=
            mul_nonneg hM2nn (div_nonneg zero_le_one (by linarith))
          have e : M2 * (1 / (16 * (1 - s)) + W0 * 2 ^ (3 - s)) =
              M2 * (1 / (16 * (1 - s))) + M2 * W0 * 2 ^ (3 - s) := by ring
          rw [e]
          exact le_add_of_nonneg_left h0

/-- The second-derivative envelope on the principal domain, with `W₀` the constant of
`integral_gradWeightOne_tail_le`. -/
lemma loopProfileD2_bound {χ ψ : ℝ → ℝ} (hχ1 : ∀ x : ℝ, |x| < 1 / 8 → χ x = 1)
    (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4)) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {M1 M2 : ℝ} (hM1 : ∀ x, |deriv χ x| ≤ M1) (hM2 : ∀ x, |deriv (deriv χ) x| ≤ M2)
    (hM1nn : 0 ≤ M1) (hM2nn : 0 ≤ M2)
    {s a K L C0 c R v : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hK : 1 ≤ K) (hL : 0 < L) (hR : 1 ≤ R) (hC0 : 0 ≤ C0) (hv : |v| ≤ L / 2)
    (hψd : |ψ v - c| ≤ C0 * ∫ t in |v|..(L / 2), gradWeightOne s a K L t)
    (hψ' : |deriv ψ v| ≤ C0 * gradWeightOne s a K L v)
    (hψ'' : |deriv (deriv ψ) v| ≤ C0 * gradWeightTwo s a K L v) :
    |loopProfileD2 χ ψ R c v| ≤
      (1 + M2 * (1 / (16 * (1 - s)) + ((1 + 1 / (1 - a)) + 1 / (1 - s)) * 2 ^ (3 - s)) +
        M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s))) * C0 * gradWeightTwo s a K L v := by
  have hw2 : 0 ≤ gradWeightTwo s a K L v := gradWeightTwo_nonneg hK
  have hT3 : |χ (v / R) * deriv (deriv ψ) v| ≤ C0 * gradWeightTwo s a K L v := by
    rw [abs_mul]
    have hχa : |χ (v / R)| ≤ 1 := by
      rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
    calc |χ (v / R)| * |deriv (deriv ψ) v| ≤ 1 * |deriv (deriv ψ) v| :=
          mul_le_mul_of_nonneg_right hχa (abs_nonneg _)
      _ ≤ C0 * gradWeightTwo s a K L v := by rw [one_mul]; exact hψ''
  have hTa := diag_term_bound hχ1 hχs hM2 hM2nn hs0 hs1 ha0 ha1 hK hL hR hC0 hv hψd
  have hTb := mixed_term_bound hχ1 hχs hM1 hM1nn hs0 hs1 ha0 ha1 hK hL hR hC0 hv hψ'
  calc |loopProfileD2 χ ψ R c v|
      = |(1 / R) * ((1 / R) * deriv (deriv χ) (v / R)) * (ψ v - c) +
          2 * ((1 / R) * deriv χ (v / R)) * deriv ψ v + χ (v / R) * deriv (deriv ψ) v| := rfl
    _ ≤ |(1 / R) * ((1 / R) * deriv (deriv χ) (v / R)) * (ψ v - c) +
          2 * ((1 / R) * deriv χ (v / R)) * deriv ψ v| + |χ (v / R) * deriv (deriv ψ) v| :=
          abs_add_le _ _
    _ ≤ (|(1 / R) * ((1 / R) * deriv (deriv χ) (v / R)) * (ψ v - c)| +
          |2 * ((1 / R) * deriv χ (v / R)) * deriv ψ v|) + |χ (v / R) * deriv (deriv ψ) v| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ M2 * (1 / (16 * (1 - s)) + ((1 + 1 / (1 - a)) + 1 / (1 - s)) * 2 ^ (3 - s)) *
          (C0 * gradWeightTwo s a K L v) +
        M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s)) * (C0 * gradWeightTwo s a K L v) +
        C0 * gradWeightTwo s a K L v := by linarith [hTa, hTb, hT3]
    _ = (1 + M2 * (1 / (16 * (1 - s)) + ((1 + 1 / (1 - a)) + 1 / (1 - s)) * 2 ^ (3 - s)) +
        M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s))) * C0 * gradWeightTwo s a K L v := by ring

/-! ## Periodicity and the cut point -/

/-- The weight `w₁` is invariant under shifts by integer multiples of the period `L`. -/
lemma gradWeightOne_add_int_mul {s a K L : ℝ} (hL : 0 < L) (t : ℝ) (n : ℤ) :
    gradWeightOne s a K L (t + n * L) = gradWeightOne s a K L t := by
  unfold gradWeightOne
  rw [circDist_add_int_mul hL t n]

/-- The weight `w₂` is invariant under shifts by integer multiples of the period `L`. -/
lemma gradWeightTwo_add_int_mul {s a K L : ℝ} (hL : 0 < L) (t : ℝ) (n : ℤ) :
    gradWeightTwo s a K L (t + n * L) = gradWeightTwo s a K L t := by
  unfold gradWeightTwo
  rw [circDist_add_int_mul hL t n]

/-- A function with a shift invariance has the same derivative at a point and at its shift. -/
lemma deriv_eq_deriv_add_of_invariant {g : ℝ → ℝ} {a : ℝ} (hg : ∀ x, g (x + a) = g x) (x : ℝ) :
    deriv g x = deriv g (x + a) := by
  have h := deriv_comp_add_const (f := g) (a := a) (x := x)
  rw [show (fun y => g (y + a)) = g from funext hg] at h
  exact h

/-- The derivative of a shift-invariant function is shift-invariant. -/
lemma deriv_invariant {g : ℝ → ℝ} {a : ℝ} (hg : ∀ x, g (x + a) = g x) :
    ∀ x, deriv g (x + a) = deriv g x :=
  fun x => (deriv_eq_deriv_add_of_invariant hg x).symm

/-- The transport vanishes near each point where the representative is at distance more than
`R/4` from the origin. -/
lemma loopTransport_zero_of_far {χ ψ : ℝ → ℝ} (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4))
    {ℓ R c : ℝ} (hR : 0 < R) (v : ℝ) (hfar : R / 4 < |loopCircleRep ℓ v|) :
    χ (loopCircleRep ℓ v / R) * (ψ (loopCircleRep ℓ v) - c) = 0 := by
  have hx : 1 / 4 < |loopCircleRep ℓ v / R| := by
    rw [abs_div, abs_of_pos hR, lt_div_iff₀ hR]
    linarith
  have hnot : loopCircleRep ℓ v / R ∉ tsupport χ := by
    intro h
    have := hχs h
    rw [Set.mem_Ioo] at this
    have := abs_lt.mpr this
    linarith
  rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]

/-! ## The envelope theorem -/

/-- **Derivative envelopes of the localized transport**, the cutoff part of Lemma 5.8.
If `ψ` is smooth and `1/ℓ`-periodic with `|ψ'| ≤ C₀ w₁` and `|ψ''| ≤ C₀ w₂`, then the transport
`ψ_γ = loopTransport χ N ℓ γ ψ` satisfies the same envelopes on the whole circle, with a constant
`C` depending only on `s`, `α` and the cutoff `χ`, and not on `N`, `ℓ`, `γ`, `ψ` or `C₀`. -/
theorem loopTransport_envelope {s α : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα : s - 1 ≤ α)
    (hα2 : α < s / 2) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4)) (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ), 0 < ℓ →
      1 ≤ (N : ℝ) * ℓ → 1 < γ → 0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      ∀ t, |deriv (loopTransport χ N ℓ γ ψ) t| ≤
          C * C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t ∧
        |deriv (deriv (loopTransport χ N ℓ γ ψ)) t| ≤
          C * C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t := by
  obtain ⟨M1, M2, hM⟩ := cutoff_deriv_bounds hχ hχc
  have hM1nn : 0 ≤ M1 := le_trans (abs_nonneg _) (hM 0).1
  have hM2nn : 0 ≤ M2 := le_trans (abs_nonneg _) (hM 0).2
  have hχ1' : ∀ x : ℝ, |x| < 1 / 8 → χ x = 1 := fun x hx => hχ1 x hx.le
  set a : ℝ := 1 - s + α with ha
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a < 1 := by linarith
  have ha1' : 0 < 1 - a := by linarith
  have hs1' : 0 < 1 - s := by linarith
  set W0 : ℝ := (1 + 1 / (1 - a)) + 1 / (1 - s) with hW0
  set C1 : ℝ := 1 + M1 * (1 / (4 * (1 - s)) + W0 * 2 ^ (2 - s)) with hC1
  set C2 : ℝ := 1 + M2 * (1 / (16 * (1 - s)) + W0 * 2 ^ (3 - s)) +
    M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s)) with hC2
  have hM1 : ∀ x, |deriv χ x| ≤ M1 := fun x => (hM x).1
  have hM2 : ∀ x, |deriv (deriv χ) x| ≤ M2 := fun x => (hM x).2
  refine ⟨max 1 (max C1 C2), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro N ℓ γ ψ C0 hℓ hK1 hγ hC0 hψ hper hbd1 hbd2 t
  set K : ℝ := (N : ℝ) * ℓ with hKdef
  have hK0 : 0 < K := by linarith
  set L : ℝ := ℓ⁻¹ with hLdef
  have hL : 0 < L := inv_pos.mpr hℓ
  have hC1le : C1 ≤ max 1 (max C1 C2) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC2le : C2 ≤ max 1 (max C1 C2) := le_trans (le_max_right _ _) (le_max_right _ _)
  have h1le : (1 : ℝ) ≤ max 1 (max C1 C2) := le_max_left _ _
  set Cm : ℝ := max 1 (max C1 C2) with hCm
  have hW0nn : 0 ≤ W0 := by
    rw [hW0]
    have h1 := div_nonneg zero_le_one ha1'.le
    have h2 := div_nonneg zero_le_one hs1'.le
    linarith
  have hC1nn : 0 ≤ C1 := by
    rw [hC1]
    refine add_nonneg zero_le_one (mul_nonneg hM1nn (add_nonneg (div_nonneg zero_le_one (by linarith)) ?_))
    exact mul_nonneg hW0nn (Real.rpow_nonneg (by norm_num) _)
  have hC2nn : 0 ≤ C2 := by
    have h1 : 0 ≤ M2 * (1 / (16 * (1 - s)) + W0 * 2 ^ (3 - s)) := by
      refine mul_nonneg hM2nn (add_nonneg (div_nonneg zero_le_one (by linarith)) ?_)
      exact mul_nonneg hW0nn (Real.rpow_nonneg (by norm_num) _)
    have h2 : 0 ≤ M1 * (1 / 2 + 2 * 8 ^ a * 2 ^ (3 - s)) := by
      refine mul_nonneg hM1nn (add_nonneg (by norm_num) ?_)
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _)
    rw [hC2]
    linarith
  have hw1nn : 0 ≤ gradWeightOne s a K L t := gradWeightOne_nonneg hK1
  have hw2nn : 0 ≤ gradWeightTwo s a K L t := gradWeightTwo_nonneg hK1
  -- Scaling: `C0 w ≤ Cm C0 w` for `Cm ≥ 1`.
  have hscale1 : C0 * gradWeightOne s a K L t ≤ Cm * C0 * gradWeightOne s a K L t := by
    have : C0 ≤ Cm * C0 := le_mul_of_one_le_left hC0 h1le
    exact mul_le_mul_of_nonneg_right this hw1nn
  have hscale2 : C0 * gradWeightTwo s a K L t ≤ Cm * C0 * gradWeightTwo s a K L t := by
    have : C0 ≤ Cm * C0 := le_mul_of_one_le_left hC0 h1le
    exact mul_le_mul_of_nonneg_right this hw2nn
  have hB1le : C1 * C0 * gradWeightOne s a K L t ≤ Cm * C0 * gradWeightOne s a K L t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1le hC0) hw1nn
  have hB2le : C2 * C0 * gradWeightTwo s a K L t ≤ Cm * C0 * gradWeightTwo s a K L t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le hC0) hw2nn
  by_cases hP : GradPartial N ℓ γ
  swap
  · -- Full window: the transport is `ψ` itself.
    have hf : loopTransport χ N ℓ γ ψ = ψ := by
      funext u
      unfold loopTransport
      simp only [hP, ↓reduceIte]
    rw [hf]
    exact ⟨le_trans (hbd1 t) hscale1, le_trans (hbd2 t) hscale2⟩
  -- Partial window: the transport is `loopProfile` composed with the representative.
  set τ : ℝ := gradT N ℓ γ with hτdef
  have hτ : τ = gradM N ℓ γ / N := by
    rw [hτdef, gradT]
    simp only [hP, ↓reduceIte]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hgradM : gradM N ℓ γ = K ^ γ := by
    unfold gradM
    rfl
  have hτpos : 0 < τ := by
    rw [hτ, hgradM]
    exact div_pos (Real.rpow_pos_of_pos hK0 γ) hNpos
  have hτ1 : τ < 1 / 8 := by
    have hP' : gradM N ℓ γ < N / 8 := hP
    rw [hτ, div_lt_iff₀ hNpos]
    linarith
  set R : ℝ := τ / ℓ with hRdef
  have hRpos : 0 < R := div_pos hτpos hℓ
  have hR0 : R ≠ 0 := hRpos.ne'
  have hRτ : R = τ * L := by
    rw [hRdef, hLdef, div_eq_mul_inv]
  have hRK : R = K ^ γ / K := by
    rw [hRdef, hτ, hgradM, hKdef]
    field_simp
  have hR1 : 1 ≤ R := by
    rw [hRK, le_div_iff₀ hK0, one_mul]
    calc K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ ≤ K ^ γ := Real.rpow_le_rpow_of_exponent_le hK1 hγ.le
  have hRL : R < L := by
    rw [hRτ]
    exact mul_lt_of_lt_one_left hL (lt_trans hτ1 (by norm_num))
  set c : ℝ := ψ (1 / (2 * ℓ)) with hcdef
  have hhalf : 1 / (2 * ℓ) = L / 2 := by
    rw [hLdef]
    field_simp
  have hcψ : c = ψ (L / 2) := by rw [hcdef, hhalf]
  have hper_rep : ∀ v, loopCircleRep ℓ (v + L) = loopCircleRep ℓ v := by
    intro v
    have := loopCircleRep_add_period hℓ v
    rw [one_div] at this
    exact this
  have hLT : ∀ u, loopTransport χ N ℓ γ ψ u = loopProfile χ ψ R c (loopCircleRep ℓ u) := by
    intro u
    unfold loopTransport loopProfile
    simp only [hP, ↓reduceIte]
    have hx : ℓ * loopCircleRep ℓ u / τ = loopCircleRep ℓ u / R := by
      rw [hRdef, div_div_eq_mul_div, mul_comm ℓ]
    rw [hx]
  have hfp : Function.Periodic (loopTransport χ N ℓ γ ψ) L := by
    intro x
    rw [hLT, hLT, hper_rep]
  -- Local identity on the principal domain.
  have hloc : ∀ u, |u| < L / 2 → loopTransport χ N ℓ γ ψ =ᶠ[𝓝 u] loopProfile χ ψ R c := by
    intro u hu
    have hu' := abs_lt.mp hu
    filter_upwards [Ioo_mem_nhds hu'.1 hu'.2] with v hv
    rw [hLT, loopCircleRep_eq_self hℓ (by rw [hhalf]; linarith [hv.1]) (by rw [hhalf]; linarith [hv.2])]
  have hD1 : ∀ u, |u| < L / 2 →
      deriv (loopTransport χ N ℓ γ ψ) u = loopProfileD1 χ ψ R c u := by
    intro u hu
    rw [(hloc u hu).deriv_eq, deriv_loopProfile hχ hψ hR0]
  have hD2 : ∀ u, |u| < L / 2 →
      deriv (deriv (loopTransport χ N ℓ γ ψ)) u = loopProfileD2 χ ψ R c u := by
    intro u hu
    rw [(hloc u hu).deriv.deriv_eq, deriv_deriv_loopProfile hχ hψ hR0]
  have hψd : ∀ u, |u| ≤ L / 2 → |ψ u - c| ≤ C0 * ∫ t in |u|..(L / 2), gradWeightOne s a K L t := by
    intro u hu
    have h := psi_sub_half_le hψ hK1 hL hper hbd1 hu
    rw [hcψ, abs_sub_comm]
    exact h
  have hB1 : ∀ u, |u| < L / 2 →
      |loopProfileD1 χ ψ R c u| ≤ C1 * C0 * gradWeightOne s a K L u := by
    intro u hu
    exact loopProfileD1_bound hχ1' hχs hχ01 hM1 hM1nn hs0 hs1 ha0 ha1 hK1 hL hR1 hC0 hu.le
      (hψd u hu.le) (hbd1 u)
  have hB2 : ∀ u, |u| < L / 2 →
      |loopProfileD2 χ ψ R c u| ≤ C2 * C0 * gradWeightTwo s a K L u := by
    intro u hu
    exact loopProfileD2_bound hχ1' hχs hχ01 hM1 hM2 hM1nn hM2nn hs0 hs1 ha0 ha1 hK1 hL hR1 hC0
      hu.le (hψd u hu.le) (hbd1 u) (hbd2 u)
  -- The cut point `-L/2`: the transport vanishes near it.
  have hzero : ∀ v, -(3 * L / 4) < v → v < -(L / 4) → loopTransport χ N ℓ γ ψ v = 0 := by
    intro v hv1 hv2
    rw [hLT]
    have hfar : R / 4 < |loopCircleRep ℓ v| := by
      have hbig : L / 4 < |loopCircleRep ℓ v| := by
        rcases le_or_gt (-(L / 2)) v with hv | hv
        · have hrep : loopCircleRep ℓ v = v := by
            exact loopCircleRep_eq_self hℓ (by rw [hhalf]; linarith) (by rw [hhalf]; linarith)
          rw [hrep, abs_of_neg (by linarith)]
          linarith
        · have hrep : loopCircleRep ℓ v = v + L := by
            rw [← hper_rep v]
            exact loopCircleRep_eq_self hℓ (by rw [hhalf]; linarith) (by rw [hhalf]; linarith)
          rw [hrep, abs_of_pos (by linarith)]
          linarith
      linarith
    have := loopTransport_zero_of_far (ψ := ψ) hχs (ℓ := ℓ) (c := c) hRpos v hfar
    unfold loopProfile
    exact this
  have hfzero : loopTransport χ N ℓ γ ψ =ᶠ[𝓝 (-(L / 2))] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds (by linarith : -(3 * L / 4) < -(L / 2))
      (by linarith : -(L / 2) < -(L / 4))] with v hv
    exact hzero v hv.1 hv.2
  -- The reduction of a general point to `r = rep t ∈ [-L/2, L/2)`.
  set m : ℤ := -⌊ℓ * t + 1 / 2⌋ with hmdef
  have hrt : loopCircleRep ℓ t = t + (m : ℝ) * L := by
    unfold loopCircleRep
    rw [hmdef, hLdef]
    push_cast
    ring
  have hfinv : ∀ x, loopTransport χ N ℓ γ ψ (x + m * L) = loopTransport χ N ℓ γ ψ x :=
    fun x => hfp.int_mul m x
  have hdinv : ∀ x, deriv (loopTransport χ N ℓ γ ψ) (x + m * L) =
      deriv (loopTransport χ N ℓ γ ψ) x := deriv_invariant hfinv
  have hd1t : deriv (loopTransport χ N ℓ γ ψ) t =
      deriv (loopTransport χ N ℓ γ ψ) (loopCircleRep ℓ t) := by
    rw [hrt]
    exact deriv_eq_deriv_add_of_invariant hfinv t
  have hd2t : deriv (deriv (loopTransport χ N ℓ γ ψ)) t =
      deriv (deriv (loopTransport χ N ℓ γ ψ)) (loopCircleRep ℓ t) := by
    rw [hrt]
    exact deriv_eq_deriv_add_of_invariant hdinv t
  have hw1r : gradWeightOne s a K L (loopCircleRep ℓ t) = gradWeightOne s a K L t := by
    rw [hrt]
    exact gradWeightOne_add_int_mul hL t m
  have hw2r : gradWeightTwo s a K L (loopCircleRep ℓ t) = gradWeightTwo s a K L t := by
    rw [hrt]
    exact gradWeightTwo_add_int_mul hL t m
  obtain ⟨hr1, hr2⟩ := loopCircleRep_mem_Ico hℓ t
  rw [hhalf] at hr1 hr2
  have hrL : -(L / 2) ≤ loopCircleRep ℓ t := hr1
  constructor
  · rw [hd1t]
    rcases eq_or_lt_of_le hrL with heq | hlt
    · -- The cut point: the derivative vanishes.
      have hz : deriv (loopTransport χ N ℓ γ ψ) (loopCircleRep ℓ t) = 0 := by
        rw [← heq, hfzero.deriv_eq, deriv_const]
      rw [hz, abs_zero]
      exact mul_nonneg (mul_nonneg (by linarith) hC0) hw1nn |> fun h => le_trans h (le_refl _) |> fun _ => by
        exact mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hC0) hw1nn
    · have habs : |loopCircleRep ℓ t| < L / 2 := abs_lt.mpr ⟨hlt, hr2⟩
      rw [hD1 _ habs]
      have := hB1 _ habs
      rw [hw1r] at this
      exact this.trans hB1le
  · rw [hd2t]
    rcases eq_or_lt_of_le hrL with heq | hlt
    · have hz : deriv (deriv (loopTransport χ N ℓ γ ψ)) (loopCircleRep ℓ t) = 0 := by
        rw [← heq]
        have h1 : deriv (loopTransport χ N ℓ γ ψ) =ᶠ[𝓝 (-(L / 2))] fun _ => (0 : ℝ) := by
          filter_upwards [hfzero.deriv] with y hy
          rw [hy, deriv_const]
        rw [h1.deriv_eq, deriv_const]
      rw [hz, abs_zero]
      exact mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hC0) hw2nn
    · have habs : |loopCircleRep ℓ t| < L / 2 := abs_lt.mpr ⟨hlt, hr2⟩
      rw [hD2 _ habs]
      have := hB2 _ habs
      rw [hw2r] at this
      exact this.trans hB2le

end

end Riesz1
