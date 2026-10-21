/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth periodic cutoffs around a marked point

Let `ζ` be a smooth function on the line with `ζ = 1` on `[-r, r]`, `ζ = 0` outside `(-2r, 2r)`
and values in `[0, 1]`. For a period `L` and a point `a`, the cutoff `markCut ζ L a` is `ζ`
evaluated at the signed distance `cutRep L (x - a)` from `x - a` to the lattice `L ℤ`.
It is smooth and `L`-periodic. Its first and second derivatives are bounded by the sup norms of
`ζ'` and `ζ''`, which do not depend on `L` once `4 r < L`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The signed distance from `t` to the lattice `L ℤ`, namely `t - L * round (t / L)`. Its
absolute value is the circular distance of `t`. -/
def cutRep (L t : ℝ) : ℝ := t - L * round (t / L)

/-- Shifting the argument by an integer multiple of the period leaves the signed distance fixed. -/
lemma cutRep_add_int_mul {L : ℝ} (hL : 0 < L) (t : ℝ) (k : ℤ) :
    cutRep L (t + k * L) = cutRep L t := by
  unfold cutRep
  rw [add_div, mul_div_cancel_right₀ _ hL.ne', round_add_intCast]
  push_cast
  ring

/-- The signed distance is the nearest-integer residual: `|cutRep L x| ≤ |x - k L|` for every
integer `k`. -/
lemma abs_cutRep_le_abs_sub_int_mul {L : ℝ} (hL : 0 < L) (x : ℝ) (k : ℤ) :
    |cutRep L x| ≤ |x - k * L| := by
  have h := round_le (x / L) k
  have e1 : cutRep L x = L * (x / L - round (x / L)) := by
    unfold cutRep
    field_simp
  have e2 : x - k * L = L * (x / L - k) := by
    field_simp
  rw [e1, e2]
  simp only [abs_mul, abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left h hL.le

/-- The signed distance is one-Lipschitz for the real line. -/
lemma abs_abs_cutRep_sub_le {L : ℝ} (hL : 0 < L) (x y : ℝ) :
    |(|cutRep L x| - |cutRep L y|)| ≤ |x - y| := by
  have key : ∀ u v : ℝ, |cutRep L u| ≤ |cutRep L v| + |u - v| := by
    intro u v
    set k : ℤ := round (v / L) with hk
    have h1 := abs_cutRep_le_abs_sub_int_mul hL u k
    have h2 : v - k * L = cutRep L v := by
      unfold cutRep
      rw [← hk]
      ring
    have h3 := abs_add_le (v - k * L) (u - v)
    rw [show v - k * L + (u - v) = u - k * L by ring, h2] at h3
    linarith
  rw [abs_le]
  constructor
  · linarith [key x y, key y x, abs_sub_comm x y]
  · linarith [key x y, key y x, abs_sub_comm x y]

/-- The signed distance is at least `L / 2` in absolute value at the midpoints of the lattice
cells, and at most `L / 2` everywhere. -/
lemma abs_cutRep_le_half {L : ℝ} (hL : 0 < L) (t : ℝ) : |cutRep L t| ≤ L / 2 := by
  have h := abs_sub_round (t / L)
  have e : cutRep L t = L * (t / L - round (t / L)) := by
    unfold cutRep
    field_simp
  rw [e, abs_mul, abs_of_pos hL]
  have := mul_le_mul_of_nonneg_left h hL.le
  linarith

/-- Rounding is locally constant away from the midpoints of the lattice cells. -/
lemma round_eq_of_abs_sub_lt {z : ℝ} {k : ℤ} (h : |z - k| < 1 / 2) : round z = k := by
  rw [round_eq_iff]
  rw [abs_lt] at h
  constructor <;> linarith [h.1, h.2]

/-- The smooth bump cutoff at the marked point `a` on the circle of length `L`: the bump `ζ`
evaluated at the signed distance from `x - a` to the lattice `L ℤ`. -/
def markCut (ζ : ℝ → ℝ) (L a x : ℝ) : ℝ := ζ (cutRep L (x - a))

/-- The cutoff is `L`-periodic. -/
lemma markCut_add_period {ζ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (a x : ℝ) :
    markCut ζ L a (x + L) = markCut ζ L a x := by
  unfold markCut
  have : x + L - a = (x - a) + ((1 : ℤ) : ℝ) * L := by push_cast; ring
  rw [this, cutRep_add_int_mul hL]

/-- Off the `2r` neighborhood of the mark, the cutoff vanishes on a neighborhood. -/
lemma eventually_abs_cutRep_gt {L : ℝ} (hL : 0 < L) (a x c : ℝ)
    (hc : c < |cutRep L (x - a)|) :
    ∀ᶠ y in 𝓝 x, c < |cutRep L (y - a)| := by
  have hε : 0 < |cutRep L (x - a)| - c := sub_pos.mpr hc
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have h1 := abs_abs_cutRep_sub_le hL (y - a) (x - a)
  have h2 : y - a - (x - a) = y - x := by ring
  rw [h2] at h1
  have h3 := (abs_le.mp h1).1
  linarith

/-- Near a point where the signed distance is less than `c`, it stays less than `c`. -/
lemma eventually_abs_cutRep_lt {L : ℝ} (hL : 0 < L) (a x c : ℝ)
    (hc : |cutRep L (x - a)| < c) :
    ∀ᶠ y in 𝓝 x, |cutRep L (y - a)| < c := by
  have hε : 0 < c - |cutRep L (x - a)| := sub_pos.mpr hc
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have h1 := abs_abs_cutRep_sub_le hL (y - a) (x - a)
  have h2 : y - a - (x - a) = y - x := by ring
  rw [h2] at h1
  have h3 := (abs_le.mp h1).2
  linarith

/-- A concrete smooth bump: one on `[-r, r]`, zero outside `(-2r, 2r)`, with values in `[0, 1]`. -/
def cutoffBump (r s : ℝ) : ℝ := 1 - Real.smoothTransition ((s ^ 2 - r ^ 2) / (3 * r ^ 2))

lemma contDiff_cutoffBump (r : ℝ) : ContDiff ℝ ∞ (cutoffBump r) := by
  unfold cutoffBump
  have hpoly : ContDiff ℝ ∞ (fun s : ℝ => (s ^ 2 - r ^ 2) / (3 * r ^ 2)) := by fun_prop
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp hpoly)

lemma cutoffBump_eq_one {r s : ℝ} (hs : |s| ≤ r) : cutoffBump r s = 1 := by
  unfold cutoffBump
  have hs2 : s ^ 2 ≤ r ^ 2 := by
    have := sq_abs s
    nlinarith [abs_nonneg s]
  have hle : (s ^ 2 - r ^ 2) / (3 * r ^ 2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
  rw [Real.smoothTransition.zero_of_nonpos hle, sub_zero]

lemma cutoffBump_eq_zero {r s : ℝ} (hr : 0 < r) (hs : 2 * r ≤ |s|) : cutoffBump r s = 0 := by
  unfold cutoffBump
  have hs2 : 4 * r ^ 2 ≤ s ^ 2 := by
    have := sq_abs s
    nlinarith [abs_nonneg s]
  have hge : 1 ≤ (s ^ 2 - r ^ 2) / (3 * r ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [Real.smoothTransition.one_of_one_le hge, sub_self]

lemma cutoffBump_mem_Icc (r s : ℝ) : cutoffBump r s ∈ Icc (0 : ℝ) 1 := by
  unfold cutoffBump
  constructor
  · linarith [Real.smoothTransition.le_one ((s ^ 2 - r ^ 2) / (3 * r ^ 2))]
  · linarith [Real.smoothTransition.nonneg ((s ^ 2 - r ^ 2) / (3 * r ^ 2))]

section Bump

variable {ζ : ℝ → ℝ} {r : ℝ}

/-- A cutoff that is zero on a neighborhood of `x` has zero first and second derivatives at `x`. -/
lemma deriv_deriv_eq_zero_of_eventually_const {f : ℝ → ℝ} {x c : ℝ}
    (h : ∀ᶠ y in 𝓝 x, f y = c) :
    deriv f x = 0 ∧ deriv (deriv f) x = 0 := by
  have h1 : f =ᶠ[𝓝 x] fun _ => c := h
  have h2 : deriv f =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [h1.deriv] with y hy
    rw [hy]
    simp
  exact ⟨by rw [h1.deriv_eq]; simp, by rw [h2.deriv_eq]; simp⟩

/-- Near a point with signed distance strictly below `L / 2`, the cutoff is a translate of `ζ`. -/
lemma eventually_markCut_eq_translate {L : ℝ} (hL : 0 < L) (ζ : ℝ → ℝ) (a x : ℝ)
    (hx : |cutRep L (x - a)| < L / 2) :
    ∃ c : ℝ, markCut ζ L a =ᶠ[𝓝 x] fun y => ζ (y - c) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round ((x - a) / L) := ⟨_, rfl⟩
  refine ⟨a + k * L, ?_⟩
  have hcr : cutRep L (x - a) = L * ((x - a) / L - k) := by
    unfold cutRep
    rw [← hk]
    field_simp
  have hk2 : |(x - a) / L - k| < 1 / 2 := by
    rw [hcr, abs_mul, abs_of_pos hL] at hx
    nlinarith
  have hcont : Continuous fun y : ℝ => |(y - a) / L - k| := by fun_prop
  filter_upwards [(hcont.tendsto x).eventually (Iio_mem_nhds hk2)] with y hy
  have hy' : |(y - a) / L - k| < 1 / 2 := hy
  have hround : round ((y - a) / L) = k := round_eq_of_abs_sub_lt hy'
  unfold markCut cutRep
  rw [hround]
  congr 1
  ring

/-- Off the open `2r` neighborhood of the mark the cutoff vanishes near `x`. -/
lemma eventually_markCut_eq_zero {L r : ℝ} (hL : 0 < L) (hζ0 : ∀ s, 2 * r ≤ |s| → ζ s = 0)
    (a x : ℝ) (hx : 2 * r < |cutRep L (x - a)|) :
    ∀ᶠ y in 𝓝 x, markCut ζ L a y = 0 := by
  filter_upwards [eventually_abs_cutRep_gt hL a x (2 * r) hx] with y hy
  exact hζ0 _ hy.le

/-- Near the mark the cutoff equals one on a neighborhood of `x`. -/
lemma eventually_markCut_eq_one {L r : ℝ} (hL : 0 < L) (hζ1 : ∀ s, |s| ≤ r → ζ s = 1)
    (a x : ℝ) (hx : |cutRep L (x - a)| < r) :
    ∀ᶠ y in 𝓝 x, markCut ζ L a y = 1 := by
  filter_upwards [eventually_abs_cutRep_lt hL a x r hx] with y hy
  exact hζ1 _ hy.le

/-- The periodic cutoff is smooth when the bump vanishes outside `(-2r, 2r)` and `4 r < L`. -/
lemma contDiff_markCut (hζ : ContDiff ℝ ∞ ζ) (hζ0 : ∀ s, 2 * r ≤ |s| → ζ s = 0)
    {L : ℝ} (hL : 0 < L) (hLr : 4 * r < L) (a : ℝ) :
    ContDiff ℝ ∞ (markCut ζ L a) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : |cutRep L (x - a)| < L / 2
  · obtain ⟨c, hc⟩ := eventually_markCut_eq_translate hL ζ a x hx
    have hsub : ContDiff ℝ ∞ (fun y : ℝ => y - c) :=
      ContDiff.sub (contDiff_id (𝕜 := ℝ) (n := ∞)) contDiff_const
    have h : ContDiffAt ℝ ∞ (fun y : ℝ => ζ (y - c)) x :=
      (hζ.comp hsub).contDiffAt
    exact h.congr_of_eventuallyEq hc
  · have hx' := not_lt.mp hx
    have hx2 : 2 * r < |cutRep L (x - a)| := by linarith
    exact contDiffAt_const.congr_of_eventuallyEq (eventually_markCut_eq_zero hL hζ0 a x hx2)

/-- The first derivative of the periodic cutoff is bounded by the sup of `ζ'`, uniformly in `L`. -/
lemma abs_deriv_markCut_le (hζ0 : ∀ s, 2 * r ≤ |s| → ζ s = 0)
    {L : ℝ} (hL : 0 < L) (hLr : 4 * r < L) {M : ℝ} (hM : ∀ s, |deriv ζ s| ≤ M) (a x : ℝ) :
    |deriv (markCut ζ L a) x| ≤ M := by
  by_cases hx : |cutRep L (x - a)| < L / 2
  · obtain ⟨c, hc⟩ := eventually_markCut_eq_translate hL ζ a x hx
    rw [hc.deriv_eq, deriv_comp_sub_const]
    exact hM _
  · have hx' := not_lt.mp hx
    have hx2 : 2 * r < |cutRep L (x - a)| := by linarith
    rw [(deriv_deriv_eq_zero_of_eventually_const
      (eventually_markCut_eq_zero hL hζ0 a x hx2)).1]
    simpa using (abs_nonneg _).trans (hM 0)

/-- The second derivative of the periodic cutoff is bounded by the sup of `ζ''`, uniformly in `L`. -/
lemma abs_deriv_deriv_markCut_le (hζ0 : ∀ s, 2 * r ≤ |s| → ζ s = 0)
    {L : ℝ} (hL : 0 < L) (hLr : 4 * r < L) {M : ℝ} (hM : ∀ s, |deriv (deriv ζ) s| ≤ M)
    (a x : ℝ) :
    |deriv (deriv (markCut ζ L a)) x| ≤ M := by
  by_cases hx : |cutRep L (x - a)| < L / 2
  · obtain ⟨c, hc⟩ := eventually_markCut_eq_translate hL ζ a x hx
    have hfun : deriv (fun y : ℝ => ζ (y - c)) = fun y => deriv ζ (y - c) :=
      funext fun y => deriv_comp_sub_const ζ c y
    rw [hc.deriv.deriv_eq, hfun, deriv_comp_sub_const]
    exact hM _
  · have hx' := not_lt.mp hx
    have hx2 : 2 * r < |cutRep L (x - a)| := by linarith
    rw [(deriv_deriv_eq_zero_of_eventually_const
      (eventually_markCut_eq_zero hL hζ0 a x hx2)).2]
    simpa using (abs_nonneg _).trans (hM 0)

/-- The bump and its first two derivatives have uniform sup bounds. -/
lemma exists_bounds_deriv_bump (hζ : ContDiff ℝ ∞ ζ) (hζ0 : ∀ s, 2 * r ≤ |s| → ζ s = 0) :
    ∃ M1 M2 : ℝ, (∀ s, |deriv ζ s| ≤ M1) ∧ (∀ s, |deriv (deriv ζ) s| ≤ M2) := by
  have hc : HasCompactSupport ζ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * r)) (b := 2 * r)) ?_
    intro s hs
    apply hζ0
    by_contra h
    have h' := not_le.mp h
    exact hs ⟨(abs_lt.mp h').1.le, (abs_lt.mp h').2.le⟩
  have hc1 : HasCompactSupport (deriv ζ) := hc.deriv
  have hc2 : HasCompactSupport (deriv (deriv ζ)) := hc1.deriv
  have hd1 : ContDiff ℝ ∞ (deriv ζ) := (contDiff_infty_iff_deriv.mp hζ).2
  have hcont1 : Continuous (deriv ζ) := hζ.continuous_deriv (by simp)
  have hcont2 : Continuous (deriv (deriv ζ)) := hd1.continuous_deriv (by simp)
  obtain ⟨M1, hM1⟩ := hcont1.bounded_above_of_compact_support hc1
  obtain ⟨M2, hM2⟩ := hcont2.bounded_above_of_compact_support hc2
  exact ⟨M1, M2, fun s => by simpa [Real.norm_eq_abs] using hM1 s,
    fun s => by simpa [Real.norm_eq_abs] using hM2 s⟩

end Bump

end Riesz1

end
end
