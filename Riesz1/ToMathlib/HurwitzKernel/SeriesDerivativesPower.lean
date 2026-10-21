/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Iterated derivatives of the power of an absolute value

For `s ∈ ℝ` the function `τ ↦ |τ| ^ (-s)` is smooth off zero, and its `j`-th derivative at a
nonzero point `t` has absolute value `|∏_{i<j} (-s - i)| · |t| ^ (-s - j)`. Translating the
argument by an integer `k` gives the terms `y ↦ |k + y| ^ (-s)` of the series defining the
kernel (Lemma 2.1, derivative claims).

The file also records that an iterated derivative depends only on the germ of the function on an
open set, which lets the formulas on the two half-lines apply to the global `iteratedDeriv`.

Lemma 2.1, derivative bounds and smoothness.
-/

@[expose] public section

open Filter Topology Set
open scoped ContDiff
namespace Riesz1

/-- Iterated derivatives at a point of an open set depend only on the germ of the function near
each point of that set. -/
lemma iteratedDeriv_congr_of_eventuallyEq (U : Set ℝ) (n : ℕ) :
    ∀ {f g : ℝ → ℝ}, (∀ x ∈ U, f =ᶠ[𝓝 x] g) → ∀ {x : ℝ}, x ∈ U →
      iteratedDeriv n f x = iteratedDeriv n g x := by
  induction n with
  | zero =>
    intro f g h x hx
    simpa using (h x hx).eq_of_nhds
  | succ n ih =>
    intro f g h x hx
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    exact ih (fun y hy => (h y hy).deriv) hx

/-- The `j`-th derivative of the power `τ ↦ τ ^ q` on the positive half-line. -/
lemma iteratedDeriv_rpow_pos (q : ℝ) (j : ℕ) :
    ∀ t : ℝ, 0 < t →
      iteratedDeriv j (fun τ : ℝ => τ ^ q) t = (∏ i ∈ Finset.range j, (q - i)) * t ^ (q - j) := by
  induction j with
  | zero =>
    intro t _
    simp
  | succ j ih =>
    intro t ht
    have hev : iteratedDeriv j (fun τ : ℝ => τ ^ q) =ᶠ[𝓝 t]
        fun τ : ℝ => (∏ i ∈ Finset.range j, (q - i)) * τ ^ (q - j) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Ioi (0 : ℝ) from ht)] with τ hτ
      exact ih τ hτ
    have hd : HasDerivAt (fun τ : ℝ => (∏ i ∈ Finset.range j, (q - i)) * τ ^ (q - j))
        ((∏ i ∈ Finset.range j, (q - i)) * ((q - j) * t ^ (q - j - 1))) t :=
      (Real.hasDerivAt_rpow_const (x := t) (p := q - j) (Or.inl ht.ne')).const_mul _
    rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv, Finset.prod_range_succ,
      show q - ((j + 1 : ℕ) : ℝ) = q - j - 1 by push_cast; ring]
    ring

/-- The `j`-th derivative of `τ ↦ |τ| ^ (-s)` at a positive point. -/
lemma iteratedDeriv_abs_rpow_pos (s : ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv j (fun τ : ℝ => |τ| ^ (-s)) t =
      (∏ i ∈ Finset.range j, (-s - i)) * t ^ (-s - j) := by
  have hev : ∀ x ∈ Ioi (0 : ℝ), (fun τ : ℝ => |τ| ^ (-s)) =ᶠ[𝓝 x] fun τ : ℝ => τ ^ (-s) := by
    intro x hx
    filter_upwards [isOpen_Ioi.mem_nhds hx] with τ hτ
    simp only [abs_of_pos (show (0 : ℝ) < τ from hτ)]
  rw [iteratedDeriv_congr_of_eventuallyEq (Ioi 0) j hev (show t ∈ Ioi (0 : ℝ) from ht),
    iteratedDeriv_rpow_pos (-s) j t ht]

/-- Absolute values of the derivatives of `τ ↦ |τ| ^ (-s)` at a nonzero point. -/
lemma abs_iteratedDeriv_abs_rpow (s : ℝ) (j : ℕ) {t : ℝ} (ht : t ≠ 0) :
    |iteratedDeriv j (fun τ : ℝ => |τ| ^ (-s)) t| =
      |∏ i ∈ Finset.range j, (-s - i)| * |t| ^ (-s - j) := by
  rcases lt_or_gt_of_ne ht with htn | htp
  · have hneg : (0 : ℝ) < -t := by linarith
    have hrefl := iteratedDeriv_comp_neg j (fun τ : ℝ => |τ| ^ (-s)) t
    simp only [abs_neg] at hrefl
    rw [hrefl, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      iteratedDeriv_abs_rpow_pos s j hneg, abs_of_neg htn, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hneg _)]
  · rw [iteratedDeriv_abs_rpow_pos s j htp, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htp _),
      abs_of_pos htp]

/-- The function `τ ↦ |τ| ^ (-s)` is smooth at every nonzero point. -/
lemma contDiffAt_abs_rpow (s : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ContDiffAt ℝ ∞ (fun τ : ℝ => |τ| ^ (-s)) t := by
  rcases lt_or_gt_of_ne ht with htn | htp
  · have hc : ContDiffAt ℝ ∞ (fun τ : ℝ => (-τ) ^ (-s)) t :=
      (Real.contDiffAt_rpow_const_of_ne (x := -t) (p := -s) (neg_ne_zero.mpr ht)).comp t
        contDiffAt_id.neg
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds htn] with τ hτ
    simp only [abs_of_neg (show τ < 0 from hτ)]
  · have hc : ContDiffAt ℝ ∞ (fun τ : ℝ => τ ^ (-s)) t :=
      Real.contDiffAt_rpow_const_of_ne (x := t) (p := -s) ht
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds htp] with τ hτ
    simp only [abs_of_pos (show 0 < τ from hτ)]

/-- The translates `z ↦ |k + z| ^ (-s)` of the kernel are smooth on every set avoiding the
collision point `z = -k`. -/
lemma contDiffOn_abs_rpow_add_int (s : ℝ) (k : ℤ) {V : Set ℝ} (hV : ∀ z ∈ V, (k : ℝ) + z ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : ℝ => |(k : ℝ) + z| ^ (-s)) V := by
  intro z hz
  have h2 : ContDiffAt ℝ ∞ (fun w : ℝ => (k : ℝ) + w) z := contDiffAt_const.add contDiffAt_id
  exact ((contDiffAt_abs_rpow s (hV z hz)).comp z h2).contDiffWithinAt

/-- Iterated derivatives of a function that is smooth on an open set are differentiable there. -/
lemma differentiableAt_iteratedDeriv_of_contDiffOn {V : Set ℝ} (hV : IsOpen V) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f V) (j : ℕ) {z : ℝ} (hz : z ∈ V) :
    DifferentiableAt ℝ (iteratedDeriv j f) z := by
  have hlt : (j : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)
  have h1 : DifferentiableOn ℝ (iteratedDerivWithin j f V) V :=
    hf.differentiableOn_iteratedDerivWithin hlt hV.uniqueDiffOn
  have h2 : iteratedDerivWithin j f V =ᶠ[𝓝 z] iteratedDeriv j f :=
    Filter.eventually_of_mem (hV.mem_nhds hz) (fun w hw => iteratedDerivWithin_of_isOpen hV hw)
  exact (h1.differentiableAt (hV.mem_nhds hz)).congr_of_eventuallyEq h2.symm

/-- The `j`-th derivative of the translate `z ↦ |k + z| ^ (-s)` at a point where `k + z ≠ 0`. -/
lemma abs_iteratedDeriv_abs_rpow_add_int (s : ℝ) (j : ℕ) (k : ℤ) {y : ℝ} (hy : (k : ℝ) + y ≠ 0) :
    |iteratedDeriv j (fun z : ℝ => |(k : ℝ) + z| ^ (-s)) y| =
      |∏ i ∈ Finset.range j, (-s - i)| * |(k : ℝ) + y| ^ (-s - j) := by
  have hfun : (fun z : ℝ => |(k : ℝ) + z| ^ (-s)) =
      fun z : ℝ => (fun τ : ℝ => |τ| ^ (-s)) (z + k) := by
    funext z
    simp only [add_comm]
  have hy' : y + (k : ℝ) ≠ 0 := by rwa [add_comm] at hy
  have hshift : iteratedDeriv j (fun z : ℝ => (fun τ : ℝ => |τ| ^ (-s)) (z + k)) y =
      iteratedDeriv j (fun τ : ℝ => |τ| ^ (-s)) (y + k) :=
    congrFun (iteratedDeriv_comp_add_const j (fun τ : ℝ => |τ| ^ (-s)) (k : ℝ)) y
  rw [hfun, hshift, add_comm (k : ℝ) y]
  exact abs_iteratedDeriv_abs_rpow s j hy'

end Riesz1
