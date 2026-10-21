/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingDisplacementEvent
public import Riesz1.Auxiliary.GradientSplittingCellsDefs
public import Riesz1.Auxiliary.GradientSplittingWindowPVLimit
public import Riesz1.Auxiliary.GradientSplittingWindowBackground
public import Riesz1.Auxiliary.GradientSplittingWindowPV
public import Riesz1.Auxiliary.GradientSplittingIdentityExist

/-!
# The background part of the reference field

The quadrature part of Lemma 5.7, first step. This module
contains the pointwise identity behind the background term of `V^{(2)}_i` and the truncated
integral of the kernel derivative `h' = deriv (gradKernelH s)` over an interval containing the
origin, where the principal value of `h'` at the origin is computed from the evenness of `h`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-! ## The pointwise identity -/

/-- Off the lattice, the two integrands of the background term differ by the derivative of the
kernel times the constant `ψ'(x/ℓ)`, plus a remainder of the form `Z_x v² g''`. -/
lemma gradQuad_pointwise (ψ : ℝ → ℝ) (ℓ : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ)
    {v : ℝ} (hv : (v : UnitAddCircle) ≠ 0) :
    gradZx ψ ℓ x (x + v) * gradKernelH s v - gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v
      = -(deriv ψ (x / ℓ) * deriv (gradKernelH s) v)
        - gradZx ψ ℓ x (x + v) * (v ^ 2 * iteratedDeriv 2 (hurwitzKernel s) v) := by
  have hv0 : v ≠ 0 := fun h => hv (by simp [h])
  have hZ : gradZ ψ ℓ x (x + v) = deriv ψ (x / ℓ) + v * gradZx ψ ℓ x (x + v) := by
    unfold gradZx
    rw [add_sub_cancel_left, mul_div_cancel₀ _ hv0]
    ring
  have hH : gradKernelH s v = v * iteratedDeriv 1 (hurwitzKernel s) v := by
    rw [gradKernelH_eq]
  have hD : deriv (gradKernelH s) v
      = iteratedDeriv 1 (hurwitzKernel s) v + v * iteratedDeriv 2 (hurwitzKernel s) v := by
    rw [← iteratedDeriv_one]
    exact gradSplit_iteratedDeriv_one_gradKernelH s hs0 hs1 hv
  rw [hZ, hH, hD]
  ring

/-! ## The kernel derivative: differentiability and the truncated integral -/

/-- The modified kernel `h = gradKernelH s` is differentiable off the lattice. -/
lemma gradKernelH_hasDerivAt {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ}
    (hr : (r : UnitAddCircle) ≠ 0) :
    HasDerivAt (gradKernelH s) (deriv (gradKernelH s) r) r := by
  have hdiff : DifferentiableAt ℝ (gradKernelH s) r :=
    ((contDiffOn_gradKernelH hs0 hs1).differentiableOn (by simp)).differentiableAt
      (gradSplit_isOpen_nonInt.mem_nhds hr)
  exact hdiff.hasDerivAt

/-- The derivative `deriv (gradKernelH s)` is continuous on every set avoiding the lattice. -/
lemma continuousOn_deriv_gradKernelH {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {S : Set ℝ}
    (hS : ∀ r ∈ S, (r : UnitAddCircle) ≠ 0) :
    ContinuousOn (deriv (gradKernelH s)) S :=
  ((contDiffOn_gradKernelH hs0 hs1).continuousOn_deriv_of_isOpen gradSplit_isOpen_nonInt
    (by simp)).mono fun r hr => hS r hr

/-- Interval integrability of `h'` on an interval avoiding the lattice. -/
lemma intervalIntegrable_deriv_gradKernelH {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {c d : ℝ}
    (hS : ∀ r ∈ uIcc c d, (r : UnitAddCircle) ≠ 0) :
    IntervalIntegrable (deriv (gradKernelH s)) volume c d :=
  (continuousOn_deriv_gradKernelH hs0 hs1 hS).intervalIntegrable

/-! ## The truncated integral of `h'` -/

/-- A point of an interval lies within the larger of the absolute values of the endpoints. -/
lemma abs_le_max_of_mem_uIcc {a b v : ℝ} (hv : v ∈ uIcc a b) :
    |v| ≤ max (|a|) (|b|) := by
  have hA : |a| ≤ max (|a|) (|b|) := le_max_left _ _
  have hB : |b| ≤ max (|a|) (|b|) := le_max_right _ _
  rcases mem_uIcc.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [neg_abs_le a, le_abs_self b]
  · refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [neg_abs_le b, le_abs_self a]

/-- A point at distance at least `δ` from `0`, lying in a ball of radius `R` with `δ ≤ 1 - R`, is
allowed: its distance to every nonzero integer is at least `δ`. -/
lemma mem_gradAllowed_of_abs_bounds {δ R v : ℝ} (hδ : δ ≤ |v|) (hR : |v| ≤ R)
    (hδR : δ ≤ 1 - R) : v ∈ gradAllowed δ := by
  intro m
  by_cases hm : m = 0
  · subst hm
    simpa using hδ
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    have h2 := abs_sub_abs_le_abs_sub (m : ℝ) v
    rw [abs_sub_comm] at h2
    linarith

/-- The truncated integral of `h'` over an interval with endpoints of length at least `δ` from
the origin, with the origin inside, is the increment of `h`: the two half-intervals contribute
`h(-δ) - h(a)` and `h(b) - h(δ)`, which cancel the central increment by evenness of `h`. -/
lemma integral_indicator_allowed_deriv_gradKernelH {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {a b δ : ℝ} (hab : a < b) (ha : a ≠ 0) (hb : b ≠ 0) (hδ : 0 < δ) (hδa : δ ≤ |a|)
    (hδb : δ ≤ |b|) (hδ1 : δ ≤ 1 - max (|a|) (|b|)) :
    ∫ v in a..b, (gradAllowed δ).indicator (deriv (gradKernelH s)) v
      = gradKernelH s b - gradKernelH s a := by
  have hM : max (|a|) (|b|) < 1 := by linarith
  -- the truncated integrand is interval integrable on every interval
  have hint : ∀ c d : ℝ, IntervalIntegrable ((gradAllowed δ).indicator (deriv (gradKernelH s)))
      volume c d := fun c d =>
    intervalIntegrable_indicator_of_continuousOn (gradAllowed_isClosed δ)
      (continuousOn_deriv_gradKernelH hs0 hs1 fun _ hr => coe_ne_zero_of_mem_gradAllowed hδ hr)
      c d
  -- on a subinterval of `[a, b]` whose points are all at least `δ` from `0`, the truncated
  -- integral is the plain one
  have whole : ∀ c d : ℝ, uIcc c d ⊆ uIcc a b → (∀ v ∈ uIcc c d, δ ≤ |v|) →
      ∫ v in c..d, (gradAllowed δ).indicator (deriv (gradKernelH s)) v
        = gradKernelH s d - gradKernelH s c := by
    intro c d hsub hδc
    have hallow : ∀ v ∈ uIcc c d, v ∈ gradAllowed δ := fun v hv =>
      mem_gradAllowed_of_abs_bounds (hδc v hv) (abs_le_max_of_mem_uIcc (hsub hv)) hδ1
    have hnz : ∀ v ∈ uIcc c d, (v : UnitAddCircle) ≠ 0 := fun v hv =>
      gradSplit_coe_ne_zero (lt_of_lt_of_le hδ (hδc v hv))
        (lt_of_le_of_lt (abs_le_max_of_mem_uIcc (hsub hv)) hM)
    rw [intervalIntegral.integral_congr (g := deriv (gradKernelH s))
      (fun v hv => Set.indicator_of_mem (hallow v hv) _)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => gradKernelH_hasDerivAt hs0 hs1 (hnz v hv))
      (intervalIntegrable_deriv_gradKernelH hs0 hs1 hnz)
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · rcases lt_or_gt_of_ne hb with hb' | hb'
    · -- both endpoints negative: every point has distance at least `|b| ≥ δ` from `0`
      rw [abs_of_neg hb'] at hδb
      apply whole a b subset_rfl
      intro v hv
      rw [uIcc_of_le hab.le] at hv
      rw [abs_of_neg (by linarith [hv.2])]
      linarith [hv.2]
    · -- the origin lies strictly inside: split at `±δ`
      have hna : a ≤ -δ := by
        rw [abs_of_neg ha'] at hδa
        linarith
      have hpb : δ ≤ b := by
        rw [abs_of_pos hb'] at hδb
        exact hδb
      have h1 := intervalIntegral.integral_add_adjacent_intervals (hint a (-δ)) (hint (-δ) b)
      have h2 := intervalIntegral.integral_add_adjacent_intervals (hint (-δ) δ) (hint δ b)
      have hmid : ∫ v in (-δ)..δ, (gradAllowed δ).indicator (deriv (gradKernelH s)) v = 0 := by
        refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_).trans (by simp)
        filter_upwards [(Set.countable_singleton δ).ae_notMem volume] with v hv hvI
        rw [uIoc_of_le (by linarith : -δ ≤ δ)] at hvI
        have hlt : v < δ := lt_of_le_of_ne hvI.2 (fun h => hv (by simp [h]))
        have hnot : v ∉ gradAllowed δ := not_mem_gradAllowed_of_abs_lt (m := 0) (by
          simp only [Int.cast_zero, sub_zero]
          rw [abs_lt]
          constructor <;> linarith [hvI.1])
        simp [Set.indicator_of_notMem hnot]
      have hleft : ∫ v in a..(-δ), (gradAllowed δ).indicator (deriv (gradKernelH s)) v
          = gradKernelH s (-δ) - gradKernelH s a := by
        apply whole a (-δ)
        · intro v hv
          exact (uIcc_subset_uIcc (left_mem_uIcc) (by
            rw [mem_uIcc]; left; constructor <;> linarith)) hv
        · intro v hv
          rw [uIcc_of_le hna] at hv
          rw [abs_of_nonpos (by linarith [hv.2])]
          linarith [hv.2]
      have hright : ∫ v in δ..b, (gradAllowed δ).indicator (deriv (gradKernelH s)) v
          = gradKernelH s b - gradKernelH s δ := by
        apply whole δ b
        · intro v hv
          exact (uIcc_subset_uIcc (by rw [mem_uIcc]; left; constructor <;> linarith)
            right_mem_uIcc) hv
        · intro v hv
          rw [uIcc_of_le hpb] at hv
          rw [abs_of_pos (by linarith [hv.1])]
          linarith [hv.1]
      have hcancel := gradSplit_gradKernelH_even s δ
      linarith [h1, h2, hmid, hleft, hright, hcancel]
  · -- `a > 0`: every point has distance at least `a ≥ δ` from `0`
    rw [abs_of_pos ha'] at hδa
    apply whole a b subset_rfl
    intro v hv
    rw [uIcc_of_le hab.le] at hv
    rw [abs_of_pos (by linarith [hv.1])]
    linarith [hv.1]

/-! ## The truncated background pair -/

/-- The shifted divided difference `v ↦ Z_x(x, x + v)` is continuous on a set avoiding `0`. -/
lemma continuousOn_gradZx_shift {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x : ℝ) {S : Set ℝ} (hS : ∀ v ∈ S, v ≠ 0) :
    ContinuousOn (fun v : ℝ => gradZx ψ ℓ x (x + v)) S := by
  have h := (contDiffOn_gradZx hψ hℓ (x := x)).continuousOn
  refine h.comp ((continuous_const.add continuous_id).continuousOn) ?_
  intro v hv
  exact fun h' => hS v hv (by linarith [h'])

/-- The shifted divided difference `v ↦ Z(x, x + v)` is continuous on a set avoiding `0`. -/
lemma continuousOn_gradZ_shift {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x : ℝ) {S : Set ℝ} (hS : ∀ v ∈ S, v ≠ 0) :
    ContinuousOn (fun v : ℝ => gradZ ψ ℓ x (x + v)) S := by
  have h := (contDiffOn_gradZ hψ hℓ (x := x)).continuousOn
  refine h.comp ((continuous_const.add continuous_id).continuousOn) ?_
  intro v hv
  exact fun h' => hS v hv (by linarith [h'])

/-- The background pair, truncated at `δ` and written in the `v`-frame: the difference of the two
truncated integrals of `Z_x h` and `Z h'` equals `-ψ'(x/ℓ)` times the truncated integral of `h'`
minus the truncated integral of `Z_x v² g''`. -/
lemma gradTrunc_pair_identity {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) {a b δ : ℝ} (hδ : 0 < δ) :
    (∫ v in a..b, (gradAllowed δ).indicator
        (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v)
      - (∫ v in a..b, (gradAllowed δ).indicator
        (fun v => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v) v)
      = -(deriv ψ (x / ℓ)) * (∫ v in a..b, (gradAllowed δ).indicator
            (deriv (gradKernelH s)) v)
        - ∫ v in a..b, (gradAllowed δ).indicator
            (fun v => gradZx ψ ℓ x (x + v) * (v ^ 2 * iteratedDeriv 2 (hurwitzKernel s) v)) v := by
  have hnz : ∀ v ∈ gradAllowed δ, v ≠ 0 := fun v hv h0 => by
    have := coe_ne_zero_of_mem_gradAllowed hδ hv
    exact this (by simp [h0])
  have hnzU : ∀ v ∈ gradAllowed δ, (v : UnitAddCircle) ≠ 0 :=
    fun v hv => coe_ne_zero_of_mem_gradAllowed hδ hv
  have hcl := gradAllowed_isClosed δ
  have hcontA : ContinuousOn (fun v : ℝ => gradZx ψ ℓ x (x + v) * gradKernelH s v)
      (gradAllowed δ) :=
    (continuousOn_gradZx_shift hψ hℓ x hnz).mul
      ((contDiffOn_gradKernelH hs0 hs1).continuousOn.mono fun v hv => hnzU v hv)
  have hcontB : ContinuousOn (fun v : ℝ => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v)
      (gradAllowed δ) :=
    (continuousOn_gradZ_shift hψ hℓ x hnz).mul
      (continuousOn_deriv_gradKernelH hs0 hs1 hnzU)
  have hcontG : ContinuousOn (fun v : ℝ => gradZx ψ ℓ x (x + v) *
      (v ^ 2 * iteratedDeriv 2 (hurwitzKernel s) v)) (gradAllowed δ) :=
    (continuousOn_gradZx_shift hψ hℓ x hnz).mul
      (((continuousOn_id.pow 2).mul
        ((gradSplit_contDiffOn_iteratedDeriv s hs0 hs1 2).continuousOn.mono fun v hv =>
          hnzU v hv)))
  have hintA := intervalIntegrable_indicator_of_continuousOn hcl hcontA a b
  have hintB := intervalIntegrable_indicator_of_continuousOn hcl hcontB a b
  have hintG := intervalIntegrable_indicator_of_continuousOn hcl hcontG a b
  have hintH : IntervalIntegrable ((gradAllowed δ).indicator (deriv (gradKernelH s))) volume a b :=
    intervalIntegrable_indicator_of_continuousOn hcl
      (continuousOn_deriv_gradKernelH hs0 hs1 hnzU) a b
  rw [← intervalIntegral.integral_sub hintA hintB, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hintH.const_mul _) hintG]
  congr 1
  funext v
  by_cases hv : v ∈ gradAllowed δ
  · simp only [Set.indicator_of_mem hv]
    have hv' : (v : UnitAddCircle) ≠ 0 := hnzU v hv
    rw [gradQuad_pointwise ψ ℓ hs0 hs1 x hv']
    ring
  · simp only [Set.indicator_of_notMem hv]
    ring

/-- The limit of the background pair as the truncation vanishes, in the `v`-frame. The
`ψ'`-coefficient is killed at an integer endpoint, where the kernel increment is not defined. -/
lemma gradTrunc_pair_limit {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) {a b : ℝ} (hab : a < b)
    (ha1 : |a| < 1) (hb1 : |b| < 1) (hq0 : a = 0 → deriv ψ (x / ℓ) = 0)
    (hq1 : b = 0 → deriv ψ (x / ℓ) = 0)
    (hG : IntervalIntegrable (fun v => gradZx ψ ℓ x (x + v) * (v ^ 2 *
      iteratedDeriv 2 (hurwitzKernel s) v)) volume a b) :
    Tendsto (fun δ : ℝ =>
        (∫ v in a..b, (gradAllowed δ).indicator
          (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v)
        - (∫ v in a..b, (gradAllowed δ).indicator
          (fun v => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v) v))
      (𝓝[>] 0)
      (𝓝 (-(deriv ψ (x / ℓ)) * (gradKernelH s b - gradKernelH s a)
        - ∫ v in a..b, gradZx ψ ℓ x (x + v) * (v ^ 2 * iteratedDeriv 2 (hurwitzKernel s) v))) := by
  have hG_lim := tendsto_allowed_integral hab.le hG
  have hG_lim' := (tendsto_const_nhds
    (x := -(deriv ψ (x / ℓ)) * (gradKernelH s b - gradKernelH s a))).sub hG_lim
  by_cases hq : deriv ψ (x / ℓ) = 0
  · -- the kernel term is absent
    refine Tendsto.congr' ?_ hG_lim'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [gradTrunc_pair_identity hψ hℓ hs0 hs1 x (mem_Ioi.mp hδ), hq]
    ring
  · have ha0 : a ≠ 0 := fun h => hq (hq0 h)
    have hb0 : b ≠ 0 := fun h => hq (hq1 h)
    have hmax : max (|a|) (|b|) < 1 := max_lt ha1 hb1
    have hδ0 : 0 < min (|a|) (min (|b|) (1 - max (|a|) (|b|))) :=
      lt_min (abs_pos.mpr ha0) (lt_min (abs_pos.mpr hb0) (by linarith))
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∫ v in a..b,
        (gradAllowed δ).indicator (deriv (gradKernelH s)) v)
          = gradKernelH s b - gradKernelH s a := by
      filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
      have hm1 := min_le_left (|a|) (min (|b|) (1 - max (|a|) (|b|)))
      have hm2 := min_le_right (|a|) (min (|b|) (1 - max (|a|) (|b|)))
      have hm3 := min_le_left (|b|) (1 - max (|a|) (|b|))
      have hm4 := min_le_right (|b|) (1 - max (|a|) (|b|))
      exact integral_indicator_allowed_deriv_gradKernelH hs0 hs1 hab ha0 hb0 hδ.1
        (by linarith [hδ.2]) (by linarith [hδ.2]) (by linarith [hδ.2])
    refine Tendsto.congr' ?_ hG_lim'
    filter_upwards [hev, self_mem_nhdsWithin] with δ hδH hδ
    rw [gradTrunc_pair_identity hψ hℓ hs0 hs1 x (mem_Ioi.mp hδ), hδH]

/-- The principal-value pair of the background term. The two principal values exist, and their
difference is the limit of the truncated difference. -/
lemma gradPV_pair_sub_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (x : ℝ)
    (hab : gradBLo N ℓ γ x - x < gradBHi N ℓ γ x - x)
    (ha1 : |gradBLo N ℓ γ x - x| < 1) (hb1 : |gradBHi N ℓ γ x - x| < 1)
    (hq0 : gradBLo N ℓ γ x - x = 0 → deriv ψ (x / ℓ) = 0)
    (hq1 : gradBHi N ℓ γ x - x = 0 → deriv ψ (x / ℓ) = 0)
    (hG : IntervalIntegrable (fun v => gradZx ψ ℓ x (x + v) * (v ^ 2 *
      iteratedDeriv 2 (hurwitzKernel s) v)) volume (gradBLo N ℓ γ x - x) (gradBHi N ℓ γ x - x)) :
    gradPV N ℓ γ x (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x))
      - gradPV N ℓ γ x (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x))
      = -(deriv ψ (x / ℓ)) * (gradKernelH s (gradBHi N ℓ γ x - x) - gradKernelH s (gradBLo N ℓ γ x - x))
        - ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
          gradZx ψ ℓ x (x + v) * (v ^ 2 * iteratedDeriv 2 (hurwitzKernel s) v) := by
  obtain ⟨LA, LB, hA, hB⟩ := gradPV_exists hψ hℓ0 hp hs0 hs1 hsupp x
  have hA' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
      (gradAllowed δ).indicator (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v)
      (𝓝[>] 0) (𝓝 LA) := by
    refine Tendsto.congr (fun δ => ?_) hA
    rw [gradPV_integral_eq_vframe]
    simp only [add_sub_cancel_left]
  have hB' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
      (gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v) v)
      (𝓝[>] 0) (𝓝 LB) := by
    refine Tendsto.congr (fun δ => ?_) hB
    rw [gradPV_integral_eq_vframe]
    simp only [add_sub_cancel_left]
  have hPA : gradPV N ℓ γ x (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) = LA :=
    hA.limUnder_eq
  have hPB : gradPV N ℓ γ x (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) = LB :=
    hB.limUnder_eq
  have hlim := gradTrunc_pair_limit hψ hℓ0 hs0 hs1 x hab ha1 hb1 hq0 hq1 hG
  have hdiff := tendsto_nhds_unique (hA'.sub hB') hlim
  rw [hPA, hPB, hdiff]

/-! ## The background term as a remainder integral -/

/-- The remainder `R_x` at the scaled point `N v` is `-N^{-s}` times the `v`-frame integrand
`Z_x(x, x+v) v² g''(v)`. -/
lemma gradCellR_mul_eq {s : ℝ} (ψ : ℝ → ℝ) (ℓ : ℝ) {N : ℕ} (hN : (N : ℝ) ≠ 0) (x v : ℝ) :
    gradCellR s N ℓ ψ x ((N : ℝ) * v)
      = -((N : ℝ) ^ (-s)) * (gradZx ψ ℓ x (x + v) * (v ^ 2 * iteratedDeriv 2 (hurwitzKernel s) v)) := by
  unfold gradCellR
  rw [mul_div_cancel_left₀ _ hN]
  ring

/-- The change of variables `w = N v` turns the remainder integral over `[N a, N b]` into
`-N^{1-s}` times the `v`-frame integral over `[a, b]`. -/
lemma integral_gradCellR_scale {s : ℝ} (ψ : ℝ → ℝ) (ℓ : ℝ) {N : ℕ}
    (hN : 0 < N) (x a b : ℝ) :
    ∫ w in ((N : ℝ) * a)..((N : ℝ) * b), gradCellR s N ℓ ψ x w
      = -((N : ℝ) ^ (1 - s)) * ∫ v in a..b,
          gradZx ψ ℓ x (x + v) * (v ^ 2 * iteratedDeriv 2 (hurwitzKernel s) v) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h : ∫ v in a..b, gradCellR s N ℓ ψ x ((N : ℝ) * v)
      = (N : ℝ)⁻¹ • ∫ w in ((N : ℝ) * a)..((N : ℝ) * b), gradCellR s N ℓ ψ x w :=
    intervalIntegral.integral_comp_mul_left (fun w => gradCellR s N ℓ ψ x w) hN0
  have hcongr : ∫ v in a..b, gradCellR s N ℓ ψ x ((N : ℝ) * v)
      = -((N : ℝ) ^ (-s)) * ∫ v in a..b,
          gradZx ψ ℓ x (x + v) * (v ^ 2 * iteratedDeriv 2 (hurwitzKernel s) v) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun v _ => gradCellR_mul_eq ψ ℓ hN0 x v
  have hpow : (N : ℝ) ^ (1 - s) = (N : ℝ) * (N : ℝ) ^ (-s) := by
    rw [show (1 - s) = 1 + (-s) by ring, Real.rpow_add hNpos, Real.rpow_one]
  rw [smul_eq_mul] at h
  rw [hpow, ← mul_inv_cancel_left₀ hN0 (∫ w in ((N : ℝ) * a)..((N : ℝ) * b),
    gradCellR s N ℓ ψ x w), ← h, hcongr]
  ring

/-- The background term of `V^{(2)}`, in closed form: the principal values of `Z_x h` and `Z h'`
combine to a boundary term `ψ'(x/ℓ)(h(b) - h(a))` and the remainder integral over `[N a, N b]`,
where `a = gradBLo - x` and `b = gradBHi - x` are the endpoints of `B` in the `v`-frame. -/
theorem gradPV_background_eq_cellR {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (x a b : ℝ) (ha : gradBLo N ℓ γ x - x = a) (hb : gradBHi N ℓ γ x - x = b)
    (hab : a < b) (ha1 : |a| < 1) (hb1 : |b| < 1)
    (hq0 : a = 0 → deriv ψ (x / ℓ) = 0) (hq1 : b = 0 → deriv ψ (x / ℓ) = 0)
    (hR : IntervalIntegrable (gradCellR s ((N : ℕ)) ℓ ψ x) volume
      (((N : ℕ) : ℝ) * a) (((N : ℕ) : ℝ) * b)) :
    -2 * ((N : ℕ) : ℝ) ^ (1 - s) * gradPV N ℓ γ x
        (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x))
      + 2 * ((N : ℕ) : ℝ) ^ (1 - s) * gradPV N ℓ γ x
        (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x))
      = 2 * ((N : ℕ) : ℝ) ^ (1 - s) * deriv ψ (x / ℓ) * (gradKernelH s b - gradKernelH s a)
        - 2 * ∫ w in (((N : ℕ) : ℝ) * a)..(((N : ℕ) : ℝ) * b), gradCellR s (N : ℕ) ℓ ψ x w := by
  have hN : (0 : ℕ) < (N : ℕ) := N.pos
  have hN0 : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hN
  -- the remainder integrand is the `v`-frame integrand, up to the factor `-N^{s}`
  have hGab : IntervalIntegrable (fun v => gradZx ψ ℓ x (x + v) * (v ^ 2 *
      iteratedDeriv 2 (hurwitzKernel s) v)) volume a b := by
    have h1 := hR.comp_mul_left (c := ((N : ℕ) : ℝ))
    rw [mul_div_cancel_left₀ _ hN0, mul_div_cancel_left₀ _ hN0] at h1
    have hfun : (fun v : ℝ => -(((N : ℕ) : ℝ) ^ s) * gradCellR s (N : ℕ) ℓ ψ x
        (((N : ℕ) : ℝ) * v)) = fun v => gradZx ψ ℓ x (x + v) * (v ^ 2 *
          iteratedDeriv 2 (hurwitzKernel s) v) := by
      funext v
      have hNs : ((N : ℕ) : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos hNpos s).ne'
      rw [gradCellR_mul_eq ψ ℓ hN0 x v, Real.rpow_neg hNpos.le]
      field_simp
    rw [← hfun]
    exact h1.const_mul _
  have hP := gradPV_pair_sub_eq hψ hℓ0 hp hs0 hs1 hsupp x (by rw [ha, hb]; exact hab)
    (by rw [ha]; exact ha1) (by rw [hb]; exact hb1)
    (fun h => hq0 (ha ▸ h)) (fun h => hq1 (hb ▸ h)) (by rw [ha, hb]; exact hGab)
  rw [ha, hb] at hP
  rw [integral_gradCellR_scale ψ ℓ (N := (N : ℕ)) N.pos x a b]
  linear_combination (-2 * ((N : ℕ) : ℝ) ^ (1 - s)) * hP

end

end Riesz1
