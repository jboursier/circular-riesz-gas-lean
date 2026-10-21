/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaledLattice
public import Riesz1.Kernel.TransportKernelBounds

/-!
# Cancellation of the singularity between transport kernels

On every fixed window strictly inside `(-1,1)`, the signed-power singularities
of two scaled kernels cancel. The difference has a differentiable extension through
zero, with a derivative bound independent of both lengths when they are at least one.
This supports the bounded-length comparison in Lemma 5.1.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz1

/-- The paired series is differentiable on any window strictly inside `(-1,1)`.
Its derivative bound is chosen before the point. -/
theorem pairSum_differentiable_window {s θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |x| < θ →
      Summable (fun k : ℕ => pairTerm s x k) ∧
      DifferentiableAt ℝ (fun z => ∑' k : ℕ, pairTerm s z k) x ∧
      |deriv (fun z => ∑' k : ℕ, pairTerm s z k) x| ≤ C := by
  let δ := 1 - θ
  let V : ℕ → ℝ := fun k =>
    2 * (1 - s) * δ ^ (s - 2) * ((k : ℝ) + 1) ^ (s - 2)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  have hsum : Summable V := by
    have hh := (summable_nat_add_iff 1).2
      (Real.summable_nat_rpow.mpr (by linarith : s - 2 < -1))
    simpa only [V, Nat.cast_add, Nat.cast_one] using hh.mul_left
      (2 * (1 - s) * δ ^ (s - 2))
  let g' : ℕ → ℝ → ℝ := fun k x =>
    (s - 1) * |x - ((k : ℝ) + 1)| ^ (s - 2) +
    (s - 1) * |x + ((k : ℝ) + 1)| ^ (s - 2)
  have hderiv (k : ℕ) (x : ℝ) (hx : x ∈ Ioo (-θ) θ) :
      HasDerivAt (fun z => pairTerm s z k) (g' k x) x := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    have ha : x - ((k : ℝ) + 1) ≠ 0 := by linarith [hx.2]
    have hb : x + ((k : ℝ) + 1) ≠ 0 := by linarith [hx.1]
    exact ((hasDerivAt_signPow ha).comp_sub_const x ((k : ℝ) + 1)).add
      ((hasDerivAt_signPow hb).comp_add_const x ((k : ℝ) + 1))
  have hbound (k : ℕ) (x : ℝ) (hx : x ∈ Ioo (-θ) θ) : ‖g' k x‖ ≤ V k := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    have hc : 0 < δ * ((k : ℝ) + 1) := by positivity
    have ha : δ * ((k : ℝ) + 1) ≤ |x - ((k : ℝ) + 1)| := by
      have hh : δ * ((k : ℝ) + 1) ≤ (k : ℝ) + δ := by nlinarith
      apply hh.trans
      apply le_abs.mpr
      right
      dsimp [δ]
      linarith [hx.2]
    have hb : δ * ((k : ℝ) + 1) ≤ |x + ((k : ℝ) + 1)| := by
      have hh : δ * ((k : ℝ) + 1) ≤ (k : ℝ) + δ := by nlinarith
      apply hh.trans
      apply le_abs.mpr
      left
      dsimp [δ]
      linarith [hx.1]
    have hp (v : ℝ) (hv : δ * ((k : ℝ) + 1) ≤ |v|) :
        |(s - 1) * |v| ^ (s - 2)| ≤
          (1 - s) * δ ^ (s - 2) * ((k : ℝ) + 1) ^ (s - 2) := by
      rw [abs_mul, abs_of_neg (by linarith : s - 1 < 0),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      have hh := Real.rpow_le_rpow_of_nonpos hc hv (by linarith : s - 2 ≤ 0)
      rw [Real.mul_rpow hδ.le (by positivity)] at hh
      nlinarith [mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ 1 - s)]
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (by dsimp [g', V]; linarith [hp _ ha, hp _ hb])
  have hzero : Summable (fun k : ℕ => pairTerm s 0 k) := by
    have heq : (fun k : ℕ => pairTerm s 0 k) = 0 := by
      funext k
      simp only [pairTerm, zero_sub, zero_add, signPow_neg', neg_add_cancel, Pi.zero_apply]
    rw [heq]
    exact summable_zero
  refine ⟨(∑' k, V k) + 1, by
    have hh : 0 ≤ ∑' k, V k := tsum_nonneg fun k => by dsimp [V]; positivity
    linarith, fun x hx => ?_⟩
  have hx' : x ∈ Ioo (-θ) θ := abs_lt.mp hx
  have hz : (0 : ℝ) ∈ Ioo (-θ) θ := ⟨by linarith, hθ0⟩
  have hd := hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioo
    (convex_Ioo (-θ) θ).isPreconnected hderiv hbound hz hzero hx'
  refine ⟨summable_of_summable_hasDerivAt_of_isPreconnected hsum isOpen_Ioo
    (convex_Ioo (-θ) θ).isPreconnected hderiv hbound hz hzero hx', hd.differentiableAt, ?_⟩
  rw [hd.deriv, ← Real.norm_eq_abs]
  exact (tsum_of_norm_bounded hsum.hasSum (fun k => hbound k x hx')).trans (by linarith)

/-- The central signed power and the paired series represent the kernel throughout
the punctured unit window, including points outside the earlier `3/4` window. -/
theorem periodicKernel_eq_add_pairs_unit {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx : |x| < 1) (hx0 : x ≠ 0) :
    periodicKernel s x = signPow s x + ∑' k : ℕ, pairTerm s x k := by
  let θ := (|x| + 1) / 2
  obtain ⟨_, _, h⟩ := pairSum_differentiable_window hs0 hs1
    (show 0 < θ by dsimp [θ]; positivity) (show θ < 1 by dsimp [θ]; linarith)
  have hi : ∀ k : ℤ, x ≠ k := by
    intro k he
    have ha : (-1 : ℝ) < k := by linarith [neg_abs_le x]
    have hb : (k : ℝ) < 1 := by linarith [le_abs_self x]
    have ha' : -1 < k := by exact_mod_cast ha
    have hb' : k < 1 := by exact_mod_cast hb
    have hk : k = 0 := by omega
    exact hx0 (by simpa only [hk, Int.cast_zero] using he)
  have heq : (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      signPow s (x - k)) = fun M => signPow s x + ∑ k ∈ Finset.range M, pairTerm s x k :=
    funext fun M => symmetric_eq_add_pairs s x M
  have hh := tendsto_symmetric_signPow hs0 hs1 hi
  rw [heq] at hh
  exact tendsto_nhds_unique hh (tendsto_const_nhds.add
    (h x (by dsimp [θ]; linarith)).1.hasSum.tendsto_sum_nat)

/-- Subtracting the signed power leaves a differentiable extension through zero.
One derivative bound works for every circle length at least one. -/
theorem exists_uniform_scaledKernel_remainder {s θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∃ H : ℝ → ℝ,
      (∀ x : ℝ, |x| < θ → DifferentiableAt ℝ H x ∧ |deriv H x| ≤ C) ∧
      ∀ x : ℝ, |x| < θ → x ≠ 0 → scaledKernel s L x = signPow s x + H x := by
  obtain ⟨C, hC, hpair⟩ := pairSum_differentiable_window hs0 hs1 hθ0 hθ1
  refine ⟨C, hC, fun L hL => ?_⟩
  have hLp : 0 < L := by linarith
  let S : ℝ → ℝ := fun z => ∑' k : ℕ, pairTerm s z k
  let H : ℝ → ℝ := fun x => L ^ (s - 1) * S (x / L)
  have hwin (x : ℝ) (hx : |x| < θ) : |x / L| < θ := by
    rw [abs_div, abs_of_pos hLp]
    exact (div_le_self (abs_nonneg x) hL).trans_lt hx
  refine ⟨H, fun x hx => ?_, fun x hx hx0 => ?_⟩
  · obtain ⟨_, hd, hb⟩ := hpair (x / L) (hwin x hx)
    have hder : HasDerivAt H (L ^ (s - 1) * (deriv S (x / L) / L)) x :=
      by
        simpa only [H, S, Function.comp_apply, id_eq, div_eq_mul_inv, one_mul] using
          (hd.hasDerivAt.comp x ((hasDerivAt_id x).div_const L)).const_mul (L ^ (s - 1))
    refine ⟨hder.differentiableAt, ?_⟩
    rw [hder.deriv]
    have heq : L ^ (s - 1) / L = L ^ (s - 2) := by
      calc L ^ (s - 1) / L = L ^ (s - 1) / L ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = L ^ ((s - 1) - 1) := (Real.rpow_sub hLp _ _).symm
        _ = _ := by congr 1; ring
    have heq' : |L ^ (s - 1) * (deriv S (x / L) / L)| =
        L ^ (s - 2) * |deriv S (x / L)| := by
      rw [abs_mul, abs_div, abs_of_pos hLp,
        abs_of_nonneg (Real.rpow_nonneg hLp.le _)]
      calc L ^ (s - 1) * (|deriv S (x / L)| / L) =
          (L ^ (s - 1) / L) * |deriv S (x / L)| := by ring
        _ = _ := by rw [heq]
    rw [heq']
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith : s - 2 ≤ 0)
    exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hLp.le _)).trans
      (by nlinarith)
  · have hdecomp := periodicKernel_eq_add_pairs_unit hs0 hs1
      ((hwin x hx).trans hθ1) (div_ne_zero hx0 hLp.ne')
    dsimp only [H, S]
    have hn : ∀ k : ℤ, x ≠ k * L := by
      intro k he
      by_cases hk : k = 0
      · exact hx0 (by simpa only [hk, Int.cast_zero, zero_mul] using he)
      · have hh : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
        have hxb : L ≤ |x| := by rw [he, abs_mul, abs_of_pos hLp]; nlinarith
        linarith
    rw [scaledKernel_eq_periodic hs0 hs1 hLp hn, hdecomp, mul_add]
    congr 1
    rw [← signPow_mul_pos hLp, mul_div_cancel₀ _ hLp.ne']

/-- The singularities of two kernels cancel on the whole inner window. The
extension includes the diagonal and has a length-independent derivative bound. -/
theorem exists_uniform_scaledKernel_difference {s θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L T : ℝ, 1 ≤ L → 1 ≤ T → ∃ H : ℝ → ℝ,
      (∀ x : ℝ, |x| < θ → DifferentiableAt ℝ H x ∧ |deriv H x| ≤ C) ∧
      ∀ x : ℝ, |x| < θ → x ≠ 0 →
        scaledKernel s L x - scaledKernel s T x = H x := by
  obtain ⟨C, hC, hrem⟩ := exists_uniform_scaledKernel_remainder hs0 hs1 hθ0 hθ1
  refine ⟨2 * C, by positivity, fun L T hL hT => ?_⟩
  obtain ⟨H, hdH, heH⟩ := hrem L hL
  obtain ⟨G, hdG, heG⟩ := hrem T hT
  refine ⟨fun x => H x - G x, fun x hx => ?_, fun x hx hx0 => ?_⟩
  · refine ⟨(hdH x hx).1.sub (hdG x hx).1, ?_⟩
    rw [deriv_fun_sub (hdH x hx).1 (hdG x hx).1]
    exact (abs_sub _ _).trans (by linarith [(hdH x hx).2, (hdG x hx).2])
  · rw [heH x hx hx0, heG x hx hx0]
    ring

end Riesz1
