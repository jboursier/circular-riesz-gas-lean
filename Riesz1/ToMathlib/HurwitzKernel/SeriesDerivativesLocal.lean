/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.DerivativeBounds
public import Riesz1.ToMathlib.HurwitzKernel.Symmetric
public import Riesz1.ToMathlib.HurwitzKernel.SeriesDerivativesPower
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Derivatives of the defining series of the Hurwitz kernel

For `0 < s < 1` the kernel `g = hurwitzKernel s` is the limit of the symmetric partial sums
`∑_{|k| ≤ M} |k + x| ^ (-s)` renormalized by a constant (Lemma 2.1).
This file proves, for every integer `j ≥ 1`:

* the sums of the `j`-th derivatives of the terms `|k + x| ^ (-s)` converge locally uniformly off
  the integers (`tendstoLocallyUniformlyOn_partial_iteratedDeriv`).
* the `j`-th derivative of `g` is the series of the `j`-th derivatives of the terms
  (`iteratedDeriv_hurwitzKernel_eq_tsum`).

The uniform bounds come from the explicit formulas of `SeriesDerivativesPower`. Near a non-integer
`x₀`, the ball of radius `|x₀ - round x₀| / 2` keeps every term `|k + x|` at least half of
`|k + x₀|`, and the exponents `-s - j < -1` make the majorants summable over `k`. The partial sums
with their renormalizing constant are treated in `Riesz1.Kernel.FundamentalSeries`.

Lemma 2.1, derivative claims.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ContDiff
namespace Riesz1

/-- The set of non-integers, as a subset of the real line. -/
lemma isOpen_nonInt : IsOpen {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
  have hset : {x : ℝ | (x : UnitAddCircle) ≠ 0} = (Set.range ((↑) : ℤ → ℝ))ᶜ := by
    ext x
    constructor
    · intro h hx
      obtain ⟨m, hm⟩ := hx
      apply h
      rw [← hm]
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨m, by simp⟩
    · intro h hx
      apply h
      obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hx
      rw [zsmul_eq_mul, mul_one] at hm
      exact ⟨m, hm⟩
  rw [hset]
  exact Int.isClosedEmbedding_coe_real.isClosed_range.isOpen_compl

/-- A nonzero point of the circle has a positive distance `|x - round x|` to the integers. -/
lemma abs_sub_round_pos {x : ℝ} (hx : (x : UnitAddCircle) ≠ 0) : 0 < |x - round x| := by
  refine abs_pos.mpr fun h => hx ?_
  have hx' : x = (round x : ℝ) := by linarith
  rw [hx']
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round x, by simp⟩

/-- The distance `|x - round x|` is at most `|k + x|` for every integer `k`. -/
lemma abs_sub_round_le_abs_add_int (x : ℝ) (k : ℤ) : |x - round x| ≤ |(k : ℝ) + x| := by
  have ht : |x - round x| ≤ 1 / 2 := abs_sub_round x
  have hkx : (k : ℝ) + x = (x - round x) + ((round x + k : ℤ) : ℝ) := by push_cast; ring
  rw [hkx]
  rcases eq_or_ne (round x + k) 0 with hm | hm
  · simp [hm]
  · have hm1 : (1 : ℝ) ≤ |((round x + k : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hm
    rcases abs_cases (x - round x) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases ((x - round x) + ((round x + k : ℤ) : ℝ)) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rcases abs_cases ((round x + k : ℤ) : ℝ) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith

/-- For `|z - x₀| < |x₀ - round x₀| / 2`, each `|k + z|` is at least half of `|k + x₀|`. -/
lemma half_abs_add_int_le_of_dist_lt {x₀ z : ℝ} (hz : |z - x₀| < |x₀ - round x₀| / 2) (k : ℤ) :
    |(k : ℝ) + x₀| / 2 ≤ |(k : ℝ) + z| := by
  have h1 := abs_sub_round_le_abs_add_int x₀ k
  have h2 := abs_sub_abs_le_abs_sub ((k : ℝ) + x₀) ((k : ℝ) + z)
  have h3 : |((k : ℝ) + x₀) - ((k : ℝ) + z)| = |z - x₀| := by
    rw [show ((k : ℝ) + x₀) - ((k : ℝ) + z) = -(z - x₀) by ring, abs_neg]
  have h4 : |x₀ - round x₀| ≤ |(k : ℝ) + x₀| := h1
  linarith

/-- On the ball of radius `|x₀ - round x₀| / 2` the centre's distance to the integers is kept:
every `|k + z|` is positive, and `z` is not an integer. -/
lemma nonInt_of_dist_lt {x₀ z : ℝ} (hx₀ : (x₀ : UnitAddCircle) ≠ 0)
    (hz : |z - x₀| < |x₀ - round x₀| / 2) : (z : UnitAddCircle) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  rw [zsmul_eq_mul, mul_one] at hm
  have h1 := half_abs_add_int_le_of_dist_lt hz (-m)
  have h2 := abs_sub_round_le_abs_add_int x₀ (-m)
  have h3 : (((-m : ℤ) : ℝ) + z) = 0 := by push_cast; linarith
  rw [h3, abs_zero] at h1
  have hpos := abs_sub_round_pos hx₀
  linarith

/-- Every translate `k + z` is nonzero when `z` is not an integer. -/
lemma add_int_ne_zero_of_nonInt {z : ℝ} (hz : (z : UnitAddCircle) ≠ 0) (k : ℤ) :
    (k : ℝ) + z ≠ 0 := by
  intro h
  apply hz
  have hz' : z = ((-k : ℤ) : ℝ) := by push_cast; linarith
  rw [hz']
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨-k, by simp⟩

/-- The translates `|k + x| ^ e` are summable over `k` for every exponent `e < -1` and every
non-integer `x`. -/
lemma summable_abs_add_int_rpow {x : ℝ} (hx : (x : UnitAddCircle) ≠ 0) {e : ℝ} (he : e < -1) :
    Summable (fun k : ℤ => |(k : ℝ) + x| ^ e) := by
  have hy0 := fract_pos_of_coe_ne_zero x hx
  have hy1 : x - (⌊x⌋ : ℝ) < 1 := by
    have := Int.fract_lt_one x
    unfold Int.fract at this
    exact this
  obtain ⟨hsum, -⟩ := summable_and_tsum_int_abs_rpow e he (x - ⌊x⌋) hy0 hy1
  let σ : ℤ ≃ ℤ := (Equiv.addLeft ⌊x⌋).trans (Equiv.neg ℤ)
  refine ((Equiv.summable_iff σ).mpr hsum).congr fun k => ?_
  show |(x - ⌊x⌋) - ((-(⌊x⌋ + k) : ℤ) : ℝ)| ^ e = |(k : ℝ) + x| ^ e
  rw [show (x - ⌊x⌋) - ((-(⌊x⌋ + k) : ℤ) : ℝ) = (k : ℝ) + x by push_cast; ring]

/-- The halved translates `(|k + x| / 2) ^ e` are summable over `k`. -/
lemma summable_half_abs_add_int_rpow {x : ℝ} (hx : (x : UnitAddCircle) ≠ 0) {e : ℝ} (he : e < -1) :
    Summable (fun k : ℤ => (|(k : ℝ) + x| / 2) ^ e) := by
  refine ((summable_abs_add_int_rpow hx he).mul_right ((2 : ℝ) ^ (-e))).congr fun k => ?_
  have ha : 0 ≤ |(k : ℝ) + x| := abs_nonneg _
  rw [Real.div_rpow ha (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]

/-- The `j`-th derivative of a translate is bounded on the ball of radius
`|x₀ - round x₀| / 2`, by a constant times the majorant `(|k + x₀| / 2) ^ (-s - j)`. -/
lemma norm_iteratedDeriv_le_ball (s : ℝ) (hs0 : 0 < s) (j : ℕ) (k : ℤ) {x₀ z : ℝ}
    (hx₀ : (x₀ : UnitAddCircle) ≠ 0) (hz : |z - x₀| < |x₀ - round x₀| / 2) :
    ‖iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) z‖ ≤
      |∏ i ∈ Finset.range j, (-s - i)| * (|(k : ℝ) + x₀| / 2) ^ (-s - j) := by
  have hpos : 0 < |(k : ℝ) + x₀| / 2 := by
    have := abs_sub_round_pos hx₀
    have := abs_sub_round_le_abs_add_int x₀ k
    linarith
  have hkz : (k : ℝ) + z ≠ 0 := by
    intro h
    have := half_abs_add_int_le_of_dist_lt hz k
    rw [h, abs_zero] at this
    linarith
  rw [Real.norm_eq_abs, abs_iteratedDeriv_abs_rpow_add_int s j k hkz]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos hpos (half_abs_add_int_le_of_dist_lt hz k)
    (by linarith [Nat.cast_nonneg (α := ℝ) j])

/-- Composing a uniformly convergent family with a map that tends to infinity keeps uniform
convergence. -/
lemma tendstoUniformlyOn_comp_tendsto {ι ι' α β : Type*} [UniformSpace β] {F : ι → α → β}
    {f : α → β} {p : Filter ι} {p' : Filter ι'} {S : Set α} {φ : ι' → ι}
    (h : TendstoUniformlyOn F f p S) (hφ : Tendsto φ p' p) :
    TendstoUniformlyOn (fun n => F (φ n)) f p' S := by
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  exact h.comp (hφ.prodMap tendsto_id)

/-- The symmetric index sets `{-M, …, M}` exhaust the integers. -/
lemma tendsto_Icc_symm_atTop :
    Tendsto (fun M : ℕ => Finset.Icc (-(M : ℤ)) (M : ℤ)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone ?_ fun k => ⟨k.natAbs, ?_⟩
  · intro a b hab
    have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
    show Finset.Icc (-(a : ℤ)) (a : ℤ) ⊆ Finset.Icc (-(b : ℤ)) (b : ℤ)
    exact Finset.Icc_subset_Icc (by linarith) (by linarith)
  · rw [Finset.mem_Icc]
    omega

/-- The `j`-th derivatives of the symmetric partial sums of the defining series converge locally
uniformly off the integers, for every `j ≥ 1` (Lemma 2.1, derivative
claims). -/
theorem tendstoLocallyUniformlyOn_partial_iteratedDeriv (s : ℝ) (hs0 : 0 < s) {j : ℕ}
    (hj : 1 ≤ j) :
    TendstoLocallyUniformlyOn
      (fun (M : ℕ) (x : ℝ) => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) x)
      (fun x : ℝ => ∑' k : ℤ, iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) x)
      atTop {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x₀ hx₀ => ?_
  have hδ : 0 < |x₀ - round x₀| / 2 := by linarith [abs_sub_round_pos hx₀]
  refine ⟨Metric.ball x₀ (|x₀ - round x₀| / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x₀ hδ), ?_⟩
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have he : -s - (j : ℝ) < -1 := by linarith
  have hsum : Summable (fun k : ℤ =>
      |∏ i ∈ Finset.range j, (-s - i)| * (|(k : ℝ) + x₀| / 2) ^ (-s - (j : ℝ))) :=
    (summable_half_abs_add_int_rpow hx₀ he).mul_left _
  have hfu : ∀ (k : ℤ) (z : ℝ), z ∈ Metric.ball x₀ (|x₀ - round x₀| / 2) →
      ‖iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) z‖ ≤
        |∏ i ∈ Finset.range j, (-s - i)| * (|(k : ℝ) + x₀| / 2) ^ (-s - (j : ℝ)) := by
    intro k z hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    exact norm_iteratedDeriv_le_ball s hs0 j k hx₀ hz
  have hunif := HasSumUniformlyOn.of_norm_le_summable (f := fun (k : ℤ) (z : ℝ) =>
    iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) z) hsum hfu
  exact tendstoUniformlyOn_comp_tendsto (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp hunif)
    tendsto_Icc_symm_atTop

/-- The derivative of the series of `j`-th derivatives is the series of the `(j+1)`-st ones, at a
non-integer point (Lemma 2.1, derivative claims). -/
lemma hasDerivAt_tsum_iteratedDeriv (s : ℝ) (hs0 : 0 < s) {j : ℕ} (hj : 1 ≤ j) {y : ℝ}
    (hy : (y : UnitAddCircle) ≠ 0) :
    HasDerivAt (fun z : ℝ => ∑' k : ℤ, iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) z)
      (∑' k : ℤ, iteratedDeriv (j + 1) (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) y) y := by
  have hδ : 0 < |y - round y| / 2 := by linarith [abs_sub_round_pos hy]
  have hmem : y ∈ Metric.ball y (|y - round y| / 2) := Metric.mem_ball_self hδ
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have he0 : -s - (j : ℝ) < -1 := by linarith
  have he : -s - ((j + 1 : ℕ) : ℝ) < -1 := by push_cast; linarith
  have hu := (summable_half_abs_add_int_rpow hy he).mul_left
    |∏ i ∈ Finset.range (j + 1), (-s - i)|
  have hball : ∀ z ∈ Metric.ball y (|y - round y| / 2), |z - y| < |y - round y| / 2 := by
    intro z hz
    rwa [Metric.mem_ball, Real.dist_eq] at hz
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (k : ℤ) (z : ℝ) => iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) z)
    (g' := fun (k : ℤ) (z : ℝ) => iteratedDeriv (j + 1) (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) z)
    (u := fun k : ℤ => |∏ i ∈ Finset.range (j + 1), (-s - i)| *
      (|(k : ℝ) + y| / 2) ^ (-s - ((j + 1 : ℕ) : ℝ)))
    (t := Metric.ball y (|y - round y| / 2)) (y₀ := y) (y := y)
    hu Metric.isOpen_ball (convex_ball _ _).isPreconnected ?_ ?_ hmem ?_ hmem
  · intro k z hz
    have hzU : (z : UnitAddCircle) ≠ 0 := nonInt_of_dist_lt hy (hball z hz)
    rw [iteratedDeriv_succ]
    exact (differentiableAt_iteratedDeriv_of_contDiffOn (V := {x : ℝ | (x : UnitAddCircle) ≠ 0})
      isOpen_nonInt (contDiffOn_abs_rpow_add_int s k
        (fun w hw => add_int_ne_zero_of_nonInt hw k)) j hzU).hasDerivAt
  · intro k z hz
    exact norm_iteratedDeriv_le_ball s hs0 (j + 1) k hy (hball z hz)
  · refine Summable.of_norm_bounded
      ((summable_half_abs_add_int_rpow hy he0).mul_left |∏ i ∈ Finset.range j, (-s - i)|) ?_
    intro k
    have h0 : |y - y| < |y - round y| / 2 := by rw [sub_self, abs_zero]; exact hδ
    exact norm_iteratedDeriv_le_ball s hs0 j k hy h0

/-- The `j`-th derivative of the kernel is the series of the `j`-th derivatives of its terms, at
every non-integer point, for every `j ≥ 1` (Lemma 2.1). -/
theorem iteratedDeriv_hurwitzKernel_eq_tsum (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {j : ℕ}
    (hj : 1 ≤ j) :
    ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      iteratedDeriv j (hurwitzKernel s) x =
        ∑' k : ℤ, iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) x := by
  induction j, hj using Nat.le_induction with
  | base =>
    intro x hx
    have hd : HasDerivAt (hurwitzKernel s)
        (∑' k : ℤ, iteratedDeriv 1 (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) x) x := by
      refine hasDerivAt_of_tendstoLocallyUniformlyOn (f := fun (M : ℕ) (y : ℝ) =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + y| ^ (-s)) -
          2 * (M : ℝ) ^ (1 - s) / (1 - s)) isOpen_nonInt
        (tendstoLocallyUniformlyOn_partial_iteratedDeriv s hs0 le_rfl) ?_ ?_ hx
      · refine Filter.Eventually.of_forall fun M y hy => ?_
        have hF : ∀ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            HasDerivAt (fun w : ℝ => |(k : ℝ) + w| ^ (-s))
              (iteratedDeriv 1 (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) y) y := by
          intro k _
          have hd0 := differentiableAt_iteratedDeriv_of_contDiffOn
            (V := {x : ℝ | (x : UnitAddCircle) ≠ 0}) isOpen_nonInt
            (contDiffOn_abs_rpow_add_int s k (fun w hw => add_int_ne_zero_of_nonInt hw k)) 0 hy
          rw [iteratedDeriv_zero] at hd0
          rw [iteratedDeriv_one]
          exact hd0.hasDerivAt
        exact (HasDerivAt.fun_sum hF).sub_const _
      · intro y hy
        exact tendsto_rieszPartialSum s hs0 hs1 y hy
    rw [iteratedDeriv_one, hd.deriv]
  | succ j hj ih =>
    intro x hx
    have hev : iteratedDeriv j (hurwitzKernel s) =ᶠ[𝓝 x]
        fun z : ℝ => ∑' k : ℤ, iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) z :=
      Filter.eventually_of_mem (isOpen_nonInt.mem_nhds hx) fun y hy => ih y hy
    rw [iteratedDeriv_succ, hev.deriv_eq, (hasDerivAt_tsum_iteratedDeriv s hs0 hj hx).deriv]

end Riesz1
