/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformPrimitive
public import Riesz1.Frozen.CompactProfile
public import Riesz1.Frozen.UnitLength

/-!
# A fixed support margin under regularization

The compact-support clause of Lemma 5.1: both the smooth
profile and its error retain one support margin, chosen before the smoothing radius.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1
namespace Internal

/-- On the central cell, circular convolution enlarges essential support by at
most half the smoothing radius. This uses the actual periodized kernel. -/
theorem circleMollify_one_eq_zero_of_support {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (p : Profile) {r h x : ℝ} (hh : 0 < h)
    (hs : ∀ᵐ y : ℝ, r ≤ |y| → zeroExtension p y = 0)
    (hhmargin : r + h / 2 < 1 / 2) (hx : |x| < 1 / 2)
    (hxr : r + h / 2 ≤ |x|) :
    circleMollify ρ 1 h (fun t : ℝ => p.val (t : UnitAddCircle)) x = 0 := by
  unfold circleMollify
  rw [intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hs, ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ y : ℝ, y ≠ 1 / 2 from
      by rw [ae_iff]; simp)] with y hy hcell hyend
  change _ = 0
  have hycell : |y| < 1 / 2 := by
    have hc : -(1 / 2 : ℝ) < y ∧ y ≤ 1 / 2 := hcell
    exact abs_lt.mpr ⟨hc.1, lt_of_le_of_ne hc.2 hyend⟩
  by_cases hyr : r ≤ |y|
  · have hz := hy hyr
    simp only [zeroExtension, hycell, ite_true] at hz
    simp only [hz, zero_mul]
  · have hyr' : |y| < r := lt_of_not_ge hyr
    have hkernel : periodMollifier ρ 1 h (x - y) = 0 := by
      unfold periodMollifier
      suffices hz : ∀ n : ℤ, scaledMollifier ρ h (x - y + n * 1) = 0 by
        simp only [hz, tsum_zero]
      intro n
      apply scaledMollifier_eq_zero hρ hh
      by_cases hn : n = 0
      · simp only [hn, Int.cast_zero, mul_one, add_zero]
        have ht := abs_sub_abs_le_abs_sub x y
        linarith
      · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
          exact_mod_cast (show (1 : ℤ) ≤ |n| from Int.one_le_abs hn)
        have ht := abs_sub_abs_le_abs_sub (n : ℝ) (-(x - y))
        rw [sub_neg_eq_add, add_comm (n : ℝ) (x - y), abs_neg] at ht
        have ht' := abs_sub x y
        simp only [mul_one]
        linarith
    simp only [hkernel, mul_zero]

end Internal

/-- The (A4) clause of Lemma 5.1, with a single positive radius cutoff
and a single support margin for both families. The smoothed function is the
circle convolution, and the error is the actual difference. -/
theorem regUniform_compactSupport (p : Profile) (hp : CompactProfile p)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ h₀ r : ℝ, 0 < h₀ ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ∃ g e : Profile, ContDiff ℝ ∞ (fun x : ℝ => g.val (x : UnitAddCircle)) ∧
          (∀ x : ℝ, g.val (x : UnitAddCircle) =
            circleMollify ρ 1 h (fun t : ℝ => p.val (t : UnitAddCircle)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          CompactProfile g ∧ CompactProfile e := by
  obtain ⟨r₀, hr₀, hr₀half, hs⟩ := hp
  let r := (r₀ + 1 / 2) / 2
  let h₀ := r - r₀
  have hr : 0 < r := by dsimp [r]; linarith
  have hrhalf : r < 1 / 2 := by dsimp [r]; linarith
  have hr₀r : r₀ < r := by dsimp [r]; linarith
  have hh₀ : 0 < h₀ := by dsimp [h₀]; linarith
  refine ⟨h₀, r, hh₀, hr, hrhalf, fun h hh hh₀ => ?_⟩
  obtain ⟨g, _, hgs, hgv, _⟩ :=
    Internal.exists_circleMollify_L2 hρ unitLength hh ⟨p.val, p.property⟩
  change Profile at g
  change (∀ x : ℝ, g.val (x : UnitAddCircle) =
    circleMollify ρ 1 h (fun t : ℝ => p.val (t : UnitAddCircle)) x) at hgv
  let e : Profile := ⟨(fun x => p.val x - g.val x), by
    exact (p.property.sub g.property).ae_eq
      (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩
  have hgzero (x : ℝ) (hx : r ≤ |x|) : zeroExtension g x = 0 := by
    by_cases hxcell : |x| < 1 / 2
    · simp only [zeroExtension, hxcell, ite_true]
      rw [hgv]
      exact Internal.circleMollify_one_eq_zero_of_support hρ p hh hs
        (by dsimp [h₀] at hh₀; linarith) hxcell (by dsimp [h₀] at hh₀; linarith)
    · simp only [zeroExtension, hxcell, ite_false]
  have hezero : ∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0 := by
    filter_upwards [hs] with x hx hxr
    have hpzero := hx (hr₀r.le.trans hxr)
    have hgzero' := hgzero x hxr
    dsimp [zeroExtension, e] at hpzero hgzero' ⊢
    split_ifs with hxcell
    · rw [ite_eq_left hxcell] at hpzero hgzero'
      rw [hpzero, hgzero', sub_self]
    · rfl
  refine ⟨g, e, hgs, hgv, fun _ => rfl, hgzero, hezero, ?_, ?_⟩
  · exact ⟨r, hr, hrhalf, ae_of_all _ hgzero⟩
  · exact ⟨r, hr, hrhalf, hezero⟩

end Riesz1
