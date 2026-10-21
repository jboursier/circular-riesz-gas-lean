/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.PeriodicZetaEuler

/-!
# Hurwitz zeta across the pole-free strip `-1 < Re w < 1`

For `0 < t < 1` the difference `ζ(w, t) - ζ(w, 1/2)` has a series representation
`hurwitzDiff t w`. It is built from the Euler series at exponent `w`, rearranged so that
its terms are bounded by `|t - 1/2| |w| |w + 1| (n + 1)^(-Re w - 2)`. This bound is summable
on `Re w > -1`, which gives analyticity there. The identity `ζ(w, t) - ζ(w, 1/2) =
hurwitzDiff t w` holds for `Re w > 0` by the Euler representation, and the identity theorem
extends it to `-1 < Re w < 1`.

Differentiating `hurwitzDiff t` in `t` gives `∂_t ζ(w, t) = -w ζ(w + 1, t)` on this strip,
which is the derivative identity of Lemma 2.1 for `-1 < Re w < 1`.
-/

public section

open Complex Set Filter Topology
open scoped ContDiff
namespace Riesz1

/-- The `n`-th term of the shifted Euler series `hurwitzDiff`: the difference of the Euler
power terms at `t` and `1/2`, minus `(t - 1/2)` times `(n + 2)^(-w) - (n + 1)^(-w)`. -/
@[expose] noncomputable def hurwitzDiffTerm (t : ℝ) (w : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1 + (t : ℂ)) ^ (-w) - ((n : ℂ) + 1 + ((1 / 2 : ℝ) : ℂ)) ^ (-w) -
    ((t : ℂ) - ((1 / 2 : ℝ) : ℂ)) * (((n : ℂ) + 2) ^ (-w) - ((n : ℂ) + 1) ^ (-w))

/-- The series representation of `ζ(w, t) - ζ(w, 1/2)` for `-1 < Re w`, obtained from the Euler
representation at exponent `w` after the correction `(t - 1/2)` is inserted. -/
@[expose] noncomputable def hurwitzDiff (t : ℝ) (w : ℂ) : ℂ :=
  (t : ℂ) ^ (-w) - ((1 / 2 : ℝ) : ℂ) ^ (-w) - ((t : ℂ) - ((1 / 2 : ℝ) : ℂ)) +
    ∑' n : ℕ, hurwitzDiffTerm t w n

/-- The term at the point `1/2` vanishes. -/
lemma hurwitzDiffTerm_half (w : ℂ) (n : ℕ) : hurwitzDiffTerm (1 / 2) w n = 0 := by
  simp [hurwitzDiffTerm]

/-- The term `hurwitzDiffTerm` is the Euler difference of its two points, minus the correction.
Each Euler term `eulerTerm` differs from its power term by a correction `c_n(w)` that does not
depend on the point, so these corrections cancel in the difference. -/
lemma hurwitzDiffTerm_eq_sub (t : ℝ) (w : ℂ) (n : ℕ) :
    hurwitzDiffTerm t w n = (eulerTerm t w n - eulerTerm (1 / 2) w n) -
      ((t : ℂ) - ((1 / 2 : ℝ) : ℂ)) * (((n : ℂ) + 2) ^ (-w) - ((n : ℂ) + 1) ^ (-w)) := by
  simp only [hurwitzDiffTerm, eulerTerm]
  ring

/-- The derivative of `hurwitzDiffTerm` in its point, at `u` with `n + 1 + u > 0`, for `w ≠ 0`:
it is `-w eulerTerm u (w + 1) n`. -/
lemma hasDerivAt_hurwitzDiffTerm {w : ℂ} (hw : w ≠ 0) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun v : ℝ => hurwitzDiffTerm v w n) (-w * eulerTerm u (w + 1) n) u := by
  have hpos : 0 < (n : ℝ) + 1 + u := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h1 := hasDerivAt_shift_cpow_real w n hpos
  have h2 : HasDerivAt (fun v : ℝ => (v : ℂ) - ((1 / 2 : ℝ) : ℂ)) 1 u := by
    have h := ((hasDerivAt_id' u).ofReal_comp).sub_const (((1 / 2 : ℝ) : ℂ))
    simpa only [Complex.ofReal_one] using h
  have h3 := (h2.mul_const (((n : ℂ) + 2) ^ (-w) - ((n : ℂ) + 1) ^ (-w)))
  have h4 := (h1.sub (hasDerivAt_const u (((n : ℂ) + 1 + ((1 / 2 : ℝ) : ℂ)) ^ (-w)))).sub h3
  have hval : -w * ((n : ℂ) + 1 + (u : ℂ)) ^ (-w - 1) - 0 -
      1 * (((n : ℂ) + 2) ^ (-w) - ((n : ℂ) + 1) ^ (-w)) = -w * eulerTerm u (w + 1) n := by
    have e1 : (1 : ℂ) - (w + 1) = -w := by ring
    have e2 : -(w + 1) = -w - 1 := by ring
    have hw' : -w ≠ 0 := neg_ne_zero.mpr hw
    simp only [eulerTerm, e1, e2]
    field_simp
    ring
  rw [hval] at h4
  convert h4 using 1
  funext v
  simp only [hurwitzDiffTerm, Pi.sub_apply]

/-- The bound on the Euler derivative: for `u ∈ [0, 1]` and `-1 < Re w`, `w ≠ 0`, the term
`-w eulerTerm u (w + 1) n` is at most `‖w‖ ‖w + 1‖ (n + 1)^(-Re w - 2)`. -/
lemma norm_hurwitzDiffTerm_deriv_le {w : ℂ} (hw : -1 < w.re) (hw0 : w ≠ 0) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    ‖-w * eulerTerm u (w + 1) n‖ ≤ ‖w‖ * (‖w + 1‖ * ((n : ℝ) + 1) ^ (-w.re - 2)) := by
  have hre : 0 < (w + 1).re := by simp only [add_re, one_re]; linarith
  have hne : w + 1 ≠ 1 := by
    intro h
    exact hw0 (by linear_combination h)
  have h := norm_eulerTerm_le u hu0 hu1 (w + 1) hre hne n
  rw [norm_mul, norm_neg]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine h.trans (le_of_eq ?_)
  congr 2
  simp only [add_re, one_re]
  ring

/-- The sum of the bounds is controlled by `(n + 1)^(-Re w - 2)`, which is summable for
`-1 < Re w`. -/
lemma summable_rpow_shift {a : ℝ} (ha : 1 < a) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-a)) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -a < -1 by linarith))
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The term `hurwitzDiffTerm` is bounded by the Euler derivative bound times `|t - 1/2|`,
uniformly for `t ∈ [0, 1]`. -/
lemma norm_hurwitzDiffTerm_le {w : ℂ} (hw : -1 < w.re) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) :
    ‖hurwitzDiffTerm t w n‖ ≤ |t - 1 / 2| * (‖w‖ * (‖w + 1‖ * ((n : ℝ) + 1) ^ (-w.re - 2))) := by
  by_cases hw0 : w = 0
  · subst hw0
    simp [hurwitzDiffTerm]
  set C : ℝ := ‖w‖ * (‖w + 1‖ * ((n : ℝ) + 1) ^ (-w.re - 2)) with hC
  have hf : ∀ v ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun v : ℝ => hurwitzDiffTerm v w n)
      (-w * eulerTerm v (w + 1) n) (Icc (0 : ℝ) 1) v := fun v hv =>
    (hasDerivAt_hurwitzDiffTerm hw0 n hv.1).hasDerivWithinAt
  have hb : ∀ v ∈ Icc (0 : ℝ) 1, ‖-w * eulerTerm v (w + 1) n‖ ≤ C := fun v hv =>
    norm_hurwitzDiffTerm_deriv_le hw hw0 hv.1 hv.2 n
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hb (convex_Icc 0 1)
    (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) (show t ∈ Icc (0 : ℝ) 1 from ⟨ht0, ht1⟩)
  simp only [hurwitzDiffTerm_half, sub_zero, Real.norm_eq_abs] at key
  rw [mul_comm]
  exact key

/-- The power series `∑ₙ hurwitzDiffTerm t w n` is summable for `-1 < Re w` and `t ∈ [0, 1]`. -/
lemma summable_hurwitzDiffTerm {w : ℂ} (hw : -1 < w.re) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Summable (fun n : ℕ => hurwitzDiffTerm t w n) := by
  have h := summable_rpow_shift (a := w.re + 2) (by linarith)
  have hg : Summable (fun n : ℕ =>
      |t - 1 / 2| * (‖w‖ * (‖w + 1‖ * ((n : ℝ) + 1) ^ (-w.re - 2)))) := by
    apply Summable.mul_left
    apply Summable.mul_left
    refine Summable.mul_left _ ?_
    refine h.congr (fun n => ?_)
    congr 1
    ring
  exact Summable.of_norm_bounded hg (fun n => norm_hurwitzDiffTerm_le hw ht0 ht1 n)

/-- The Hurwitz zeta function at a point `x` and exponent `w`, as a function of the exponent, is
`hurwitzAt`. The telescoping series `∑ₙ ((n + 2)^(-w) - (n + 1)^(-w))` sums to `-1` for
`Re w > 0`. -/
lemma hasSum_telescope_cpow {w : ℂ} (hw : 0 < w.re) :
    HasSum (fun n : ℕ => ((n : ℂ) + 2) ^ (-w) - ((n : ℂ) + 1) ^ (-w)) (-1) := by
  have hbound : Summable (fun n : ℕ => ‖w‖ * ((n : ℝ) + 1) ^ (-w.re - 1)) := by
    refine Summable.mul_left _ ((summable_rpow_shift (a := w.re + 1) (by linarith)).congr
      (fun n => ?_))
    congr 1
    ring
  have hs : Summable (fun n : ℕ => ((n : ℂ) + 2) ^ (-w) - ((n : ℂ) + 1) ^ (-w)) := by
    refine Summable.of_norm_bounded hbound (fun n => ?_)
    have h := norm_cpow_sub_le w hw ((n : ℝ) + 1) ((n : ℝ) + 1) ((n : ℝ) + 2) (by positivity)
      ⟨le_refl _, by linarith⟩ ⟨by linarith, by linarith⟩
    push_cast at h
    exact h
  refine hs.hasSum_iff_tendsto_nat.mpr ?_
  set g : ℕ → ℂ := fun i => ((i : ℂ) + 1) ^ (-w) with hg
  have hpartial : ∀ N : ℕ, ∑ i ∈ Finset.range N, (((i : ℂ) + 2) ^ (-w) - ((i : ℂ) + 1) ^ (-w)) =
      g N - 1 := by
    intro N
    have h := Finset.sum_range_sub g N
    have hterm : ∀ i : ℕ, ((i : ℂ) + 2) ^ (-w) - ((i : ℂ) + 1) ^ (-w) = g (i + 1) - g i := by
      intro i
      simp only [hg]
      congr 2
      push_cast
      ring
    simp only [hterm]
    rw [h]
    simp [hg]
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h := (tendsto_natCast_cpow_zero (-w) (by simpa using hw)).comp (tendsto_add_atTop_nat 1)
    refine h.congr (fun n => ?_)
    simp only [Function.comp_def, hg]
    push_cast
    rfl
  have : Tendsto (fun N : ℕ => g N - 1) atTop (𝓝 (0 - 1)) := hlim.sub_const 1
  simp only [zero_sub] at this
  exact (funext hpartial ▸ this)

/-- The Euler identity for `Re w > 0`: `ζ(w, t) - ζ(w, 1/2) = hurwitzDiff t w` for `t ∈ (0, 1)`.
Both sides are the Euler series, rearranged. The Euler corrections at `t` and `1/2` cancel. -/
theorem hurwitzAt_sub_eq_hurwitzDiff_of_re_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {w : ℂ}
    (hw : 0 < w.re) (hw1 : w ≠ 1) :
    hurwitzAt t w - hurwitzAt (1 / 2) w = hurwitzDiff t w := by
  have hT := euler_eq_hurwitzZeta t ht0 ht1 w hw hw1
  have hH := euler_eq_hurwitzZeta (1 / 2) (by norm_num) (by norm_num) w hw hw1
  have hST := summable_eulerTerm t ht0.le ht1 w hw hw1
  have hSH := summable_eulerTerm (1 / 2) (by norm_num) (by norm_num) w hw hw1
  have hΔ := (hasSum_telescope_cpow hw).mul_left ((t : ℂ) - ((1 / 2 : ℝ) : ℂ))
  have hsumD : HasSum (fun n : ℕ => hurwitzDiffTerm t w n)
      ((∑' n, eulerTerm t w n - ∑' n, eulerTerm (1 / 2) w n) -
        ((t : ℂ) - ((1 / 2 : ℝ) : ℂ)) * (-1)) := by
    have hfun : (fun n : ℕ => hurwitzDiffTerm t w n) = fun n : ℕ =>
        (eulerTerm t w n - eulerTerm (1 / 2) w n) -
          ((t : ℂ) - ((1 / 2 : ℝ) : ℂ)) * (((n : ℂ) + 2) ^ (-w) - ((n : ℂ) + 1) ^ (-w)) :=
      funext (hurwitzDiffTerm_eq_sub t w)
    rw [hfun]
    exact (hST.hasSum.sub hSH.hasSum).sub hΔ
  have htsum := hsumD.tsum_eq
  unfold hurwitzAt at hT hH ⊢
  unfold hurwitzDiff
  rw [htsum, ← hT, ← hH]
  ring

/-- The Hurwitz zeta difference `hurwitzDiff` is holomorphic in the exponent on `-1 < Re w`,
for `t ∈ (0, 1)`. The terms are entire, and the series converges locally uniformly by the bound
`summable_hurwitzDiffTerm`. -/
theorem differentiableAt_hurwitzDiff {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {w₀ : ℂ}
    (hw₀ : -1 < w₀.re) :
    DifferentiableAt ℂ (fun w : ℂ => hurwitzDiff t w) w₀ := by
  have hcpow : ∀ c : ℂ, c ≠ 0 → ∀ w : ℂ, DifferentiableAt ℂ (fun v : ℂ => c ^ (-v)) w :=
    fun c hc w => (differentiableAt_id.neg).const_cpow (Or.inl hc)
  set σ : ℝ := (w₀.re - 1) / 2 with hσ
  set R : ℝ := ‖w₀‖ + 1 with hR
  let U : Set ℂ := {w : ℂ | σ < w.re ∧ ‖w‖ < R}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hw₀U : w₀ ∈ U := by
    refine ⟨?_, ?_⟩
    · simp only [hσ]; linarith
    · have := norm_nonneg w₀
      simp only [hR]; linarith
  have hσ1 : -1 < σ := by simp only [hσ]; linarith
  have hsum : Summable (fun n : ℕ =>
      |t - 1 / 2| * (R * ((R + 1) * ((n : ℝ) + 1) ^ (-σ - 2)))) := by
    refine Summable.mul_left _ (Summable.mul_left _ (Summable.mul_left _
      ((summable_rpow_shift (a := σ + 2) (by linarith)).congr (fun n => ?_))))
    congr 1
    ring
  have hdiffTerm : ∀ n : ℕ, DifferentiableOn ℂ (fun w : ℂ => hurwitzDiffTerm t w n) U := by
    intro n w _
    have hb1 : ((n : ℂ) + 1 + (t : ℂ)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hb2 : ((n : ℂ) + 1 + ((1 / 2 : ℝ) : ℂ)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hb3 : ((n : ℂ) + 2) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hb4 : ((n : ℂ) + 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact (((hcpow _ hb1 w).sub (hcpow _ hb2 w)).sub
      ((differentiableAt_const _).mul ((hcpow _ hb3 w).sub (hcpow _ hb4 w)))).differentiableWithinAt
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖hurwitzDiffTerm t w n‖ ≤
      |t - 1 / 2| * (R * ((R + 1) * ((n : ℝ) + 1) ^ (-σ - 2))) := by
    intro n w hw
    obtain ⟨hwσ, hwR⟩ := hw
    have hw1 : -1 < w.re := by linarith
    refine (norm_hurwitzDiffTerm_le hw1 ht0.le ht1 n).trans ?_
    have hnorm : ‖w‖ ≤ R := hwR.le
    have hnorm1 : ‖w + 1‖ ≤ R + 1 := by
      have := norm_add_le w 1
      simp only [norm_one] at this
      linarith
    have hpow : ((n : ℝ) + 1) ^ (-w.re - 2) ≤ ((n : ℝ) + 1) ^ (-σ - 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
    gcongr
  have hTsum : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, hurwitzDiffTerm t w n) U :=
    differentiableOn_tsum_of_summable_norm hsum hdiffTerm hU hbound
  have hS := (hTsum.differentiableAt (hU.mem_nhds hw₀U))
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (t : ℂ) ^ (-w)) w₀ :=
    hcpow _ (by exact_mod_cast ht0.ne') w₀
  have hb0 : ((1 / 2 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hpow2 : DifferentiableAt ℂ (fun w : ℂ => ((1 / 2 : ℝ) : ℂ) ^ (-w)) w₀ :=
    hcpow _ hb0 w₀
  have hfun : (fun w : ℂ => hurwitzDiff t w) = fun w : ℂ =>
      (t : ℂ) ^ (-w) - ((1 / 2 : ℝ) : ℂ) ^ (-w) - ((t : ℂ) - ((1 / 2 : ℝ) : ℂ)) +
        ∑' n : ℕ, hurwitzDiffTerm t w n := rfl
  rw [hfun]
  exact ((hpow.sub hpow2).sub (differentiableAt_const _)).add hS

/-- The derivative in the point `t ∈ (0, 1)` of `hurwitzDiff`: for `-1 < Re w` and `w ≠ 0`,
`∂_t hurwitzDiff t w = -w ζ(w + 1, t)`. The termwise derivative series are dominated by the
bound of `norm_hurwitzDiffTerm_deriv_le`, and the power term gives `-w t^(-w-1)`. -/
theorem hasDerivAt_hurwitzDiff {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {w : ℂ} (hw : -1 < w.re)
    (hw0 : w ≠ 0) :
    HasDerivAt (fun v : ℝ => hurwitzDiff v w) (-w * hurwitzAt t (w + 1)) t := by
  have hA : HasDerivAt (fun v : ℝ => (v : ℂ) ^ (-w)) ((-w) * (t : ℂ) ^ (-w - 1)) t :=
    hasDerivAt_ofReal_cpow_const ht0.ne' (neg_ne_zero.mpr hw0)
  have hB : HasDerivAt (fun v : ℝ => (v : ℂ) - ((1 / 2 : ℝ) : ℂ)) 1 t := by
    have h := ((hasDerivAt_id' t).ofReal_comp).sub_const (((1 / 2 : ℝ) : ℂ))
    simpa only [Complex.ofReal_one] using h
  have hu : Summable (fun n : ℕ => ‖w‖ * (‖w + 1‖ * ((n : ℝ) + 1) ^ (-w.re - 2))) := by
    refine Summable.mul_left _ (Summable.mul_left _
      ((summable_rpow_shift (a := w.re + 2) (by linarith)).congr (fun n => ?_)))
    congr 1
    ring
  have hC : HasDerivAt (fun v : ℝ => ∑' n : ℕ, hurwitzDiffTerm v w n)
      (∑' n : ℕ, -w * eulerTerm t (w + 1) n) t :=
    hasDerivAt_tsum_of_isPreconnected (g := fun n v => hurwitzDiffTerm v w n)
      (g' := fun n y => -w * eulerTerm y (w + 1) n) hu isOpen_Ioo isPreconnected_Ioo
      (fun n y hy => hasDerivAt_hurwitzDiffTerm hw0 n hy.1.le)
      (fun n y hy => norm_hurwitzDiffTerm_deriv_le hw hw0 hy.1.le hy.2.le n)
      ⟨ht0, ht1⟩ (summable_hurwitzDiffTerm hw ht0.le ht1.le) ⟨ht0, ht1⟩
  have hD := ((hA.sub_const (((1 / 2 : ℝ) : ℂ) ^ (-w))).sub hB).add hC
  have hre : 0 < (w + 1).re := by simp only [add_re, one_re]; linarith
  have hne : w + 1 ≠ 1 := fun h => hw0 (by linear_combination h)
  have hE := (euler_eq_hurwitzZeta t ht0 ht1.le (w + 1) hre hne).symm
  have hval : (-w * (t : ℂ) ^ (-w - 1) - 1) + ∑' n : ℕ, -w * eulerTerm t (w + 1) n =
      -w * hurwitzAt t (w + 1) := by
    have e1 : (1 : ℂ) - (w + 1) = -w := by ring
    have e2 : -(w + 1) = -w - 1 := by ring
    have hwne : w ≠ 0 := hw0
    unfold hurwitzAt
    rw [tsum_mul_left, hE, e1, e2]
    field_simp
    ring
  have hfun : (fun v : ℝ => hurwitzDiff v w) = fun v : ℝ =>
      (v : ℂ) ^ (-w) - ((1 / 2 : ℝ) : ℂ) ^ (-w) - ((v : ℂ) - ((1 / 2 : ℝ) : ℂ)) +
        ∑' n : ℕ, hurwitzDiffTerm v w n := rfl
  rw [hfun, ← hval]
  exact hD

/-- The identity `ζ(w, t) - ζ(w, 1/2) = hurwitzDiff t w` holds on the strip `-1 < Re w < 1`.
It holds on the open half plane `Re w > 0`, by `hurwitzAt_sub_eq_hurwitzDiff_of_re_pos`. The
identity theorem transfers it along a preconnected set `U` that avoids the pole `w = 1`, lies in
`{-1 < Re w}`, and contains both `w₀` and `2`. The set `U` is the image of `{1}ᶜ` under the map
that clamps the real part at `c = (Re w₀ - 1)/2`, as in `Euler.lean`. -/
theorem hurwitzAt_sub_eq_hurwitzDiff {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {w₀ : ℂ}
    (hw₀ : -1 < w₀.re) (hw₀' : w₀.re < 1) :
    hurwitzAt t w₀ - hurwitzAt (1 / 2) w₀ = hurwitzDiff t w₀ := by
  set O : Set ℂ := {w : ℂ | -1 < w.re} ∩ {1}ᶜ with hO
  have hOopen : IsOpen O :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  set c : ℝ := (w₀.re - 1) / 2 with hc
  have hc1 : -1 < c := by simp only [hc]; linarith
  have hc2 : c < 0 := by simp only [hc]; linarith
  let f : ℂ → ℂ := fun z => ((max c z.re : ℝ) : ℂ) + (z.im : ℂ) * I
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  let U : Set ℂ := f '' {1}ᶜ
  have hU : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected.image f
      hf.continuousOn
  have hUO : U ⊆ O := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, ?_⟩
    · show -1 < (f v).re
      simp only [f, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
        add_zero, mul_one, ofReal_re]
      exact lt_of_lt_of_le hc1 (le_max_left _ _)
    · intro h
      apply hv
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [f, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
        add_zero, mul_one, add_im, mul_im, one_im, one_re,
        zero_add, ofReal_im] at hre him
      rcases le_total c v.re with h1 | h1
      · rw [max_eq_right h1] at hre
        exact Complex.ext hre him
      · rw [max_eq_left h1] at hre
        linarith
  have hw₀U : w₀ ∈ U := by
    refine ⟨w₀, ?_, ?_⟩
    · show w₀ ∈ ({1}ᶜ : Set ℂ)
      intro h
      rw [h] at hw₀'
      simp at hw₀'
    · apply Complex.ext
      · simp only [f, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
          zero_mul, add_zero]
        exact max_eq_right (by linarith)
      · simp only [f, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one, mul_zero,
          zero_add, add_zero]
  have h2U : (2 : ℂ) ∈ U := by
    refine ⟨2, ?_, ?_⟩
    · show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)
      norm_num
    · apply Complex.ext
      · simp only [f, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
          zero_mul, add_zero, Complex.re_ofNat]
        exact max_eq_right (by linarith)
      · simp only [f, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one, mul_zero,
          add_zero, Complex.im_ofNat]
  let Φ : ℂ → ℂ := fun w => hurwitzAt t w - hurwitzAt (1 / 2) w - hurwitzDiff t w
  have hΦ : DifferentiableOn ℂ Φ O := by
    intro w hw
    have hw1 : -1 < w.re := hw.1
    have hw2 : w ≠ 1 := hw.2
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((HurwitzZeta.differentiableAt_hurwitzZeta (t : UnitAddCircle) hw2).sub
      (HurwitzZeta.differentiableAt_hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) hw2)).sub
      (differentiableAt_hurwitzDiff ht0 ht1 hw1)
  have hΦan : AnalyticOnNhd ℂ Φ O := hΦ.analyticOnNhd hOopen
  have heq2 : Φ =ᶠ[𝓝 (2 : ℂ)] fun _ : ℂ => (0 : ℂ) := by
    have hopen : IsOpen ({z : ℂ | 0 < z.re} ∩ {1}ᶜ) :=
      (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
    filter_upwards [hopen.mem_nhds ⟨by norm_num, by norm_num⟩] with z hz
    have hid := hurwitzAt_sub_eq_hurwitzDiff_of_re_pos ht0 ht1 hz.1 hz.2
    show hurwitzAt t z - hurwitzAt (1 / 2) z - hurwitzDiff t z = 0
    rw [hid, sub_self]
  have hEq := hΦan.mono (show U ⊆ O from hUO) |>.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hU h2U heq2
  have hval := hEq hw₀U
  simp only [Φ] at hval
  linear_combination hval

/-- The derivative in `t ∈ (0, 1)` of `ζ(w, t)` for `-1 < Re w < 1` and `w ≠ 0`:
`∂_t ζ(w, t) = -w ζ(w + 1, t)`. This is part of Lemma 2.1, in the strip
`-1 < Re w < 1`, obtained from `hurwitzDiff` by the identity theorem. -/
theorem hasDerivAt_hurwitzAt_of_re_gt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {w : ℂ}
    (hw : -1 < w.re) (hw' : w.re < 1) (hw0 : w ≠ 0) :
    HasDerivAt (fun v : ℝ => hurwitzAt v w) (-w * hurwitzAt t (w + 1)) t := by
  have hd := (hasDerivAt_hurwitzDiff ht0 ht1 hw hw0).const_add (hurwitzAt (1 / 2) w)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht0 ht1] with v hv
  have hid := hurwitzAt_sub_eq_hurwitzDiff hv.1 hv.2.le hw hw'
  show hurwitzAt v w = hurwitzAt (1 / 2) w + hurwitzDiff v w
  linear_combination hid

end Riesz1

end
