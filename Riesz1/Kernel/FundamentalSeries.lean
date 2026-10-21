/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Regularity
public import Riesz1.ToMathlib.HurwitzKernel.Mean
public import Riesz1.ToMathlib.HurwitzKernel.Derivatives
public import Riesz1.ToMathlib.HurwitzKernel.DerivativeBounds
public import Riesz1.ToMathlib.HurwitzKernel.SeriesDerivativesLocal
public import Riesz1.Frozen.RieszRepresentative

/-!
# The convergent kernel, its derivatives and its mean

The assembled statement of the series part of Lemma 2.1, for the kernel
`Riesz1.rieszRepresentative`. The theorem `Riesz1.fundamental_series`
collects the claims of the lemma: the convergence of the renormalized symmetric partial sums
off the integers, smoothness, evenness and periodicity, the formula on `(0, 1)` in terms of the
Hurwitz zeta function, integrability and mean zero, the smooth remainder at zero, locally uniform
convergence of every derivative of order at least one, the series formula for the second
derivative, the derivative bounds, and the lower bound and the blow-up at zero.

The derivative claims are proved in `Riesz1.ToMathlib.HurwitzKernel.SeriesDerivativesLocal`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ContDiff
namespace Riesz1

/-- The renormalized symmetric partial sums of the kernel, differentiated `j` times, converge
locally uniformly off the integers to the `j`-th derivative of the kernel, for every `j ≥ 1`
(the derivative claims of Lemma 2.1). -/
theorem tendstoLocallyUniformlyOn_partialSum_iteratedDeriv (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    {j : ℕ} (hj : 1 ≤ j) :
    TendstoLocallyUniformlyOn
      (fun (M : ℕ) (x : ℝ) => iteratedDeriv j (fun y : ℝ =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + y| ^ (-s)) -
          2 * (M : ℝ) ^ (1 - s) / (1 - s)) x)
      (iteratedDeriv j (hurwitzKernel s)) atTop {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
  -- The renormalizing constant does not contribute to derivatives of order `j ≥ 1`.
  have hconst : ∀ (f : ℝ → ℝ) (c : ℝ),
      iteratedDeriv j (fun y => f y - c) = iteratedDeriv j f := by
    intro f c
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_sub_const_fun]
  have hT : {x : ℝ | (x : UnitAddCircle) ≠ 0}.EqOn
      (fun x : ℝ => ∑' k : ℤ, iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) x)
      (iteratedDeriv j (hurwitzKernel s)) := fun x hx =>
    (iteratedDeriv_hurwitzKernel_eq_tsum s hs0 hs1 hj x hx).symm
  have hP : ∀ M : ℕ, {x : ℝ | (x : UnitAddCircle) ≠ 0}.EqOn
      (fun x : ℝ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) x)
      (fun x : ℝ => iteratedDeriv j (fun y : ℝ =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + y| ^ (-s)) -
          2 * (M : ℝ) ^ (1 - s) / (1 - s)) x) := by
    intro M x hx
    have hsmooth : ∀ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ContDiffAt ℝ j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) x := fun k _ =>
      (((contDiffOn_abs_rpow_add_int s k (V := {x : ℝ | (x : UnitAddCircle) ≠ 0})
        (fun w hw => add_int_ne_zero_of_nonInt hw k)) x hx).contDiffAt
        (isOpen_nonInt.mem_nhds hx)).of_le (by exact_mod_cast le_top)
    have h1 := hconst (fun y : ℝ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + y| ^ (-s))
      (2 * (M : ℝ) ^ (1 - s) / (1 - s))
    have h2 := iteratedDeriv_fun_sum (n := j) (x := x)
      (f := fun (k : ℤ) (w : ℝ) => |(k : ℝ) + w| ^ (-s)) (I := Finset.Icc (-(M : ℤ)) (M : ℤ))
      hsmooth
    show ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), iteratedDeriv j (fun w : ℝ => |(k : ℝ) + w| ^ (-s)) x
      = iteratedDeriv j (fun y : ℝ =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + y| ^ (-s)) -
          2 * (M : ℝ) ^ (1 - s) / (1 - s)) x
    rw [h1, h2]
  exact ((tendstoLocallyUniformlyOn_partial_iteratedDeriv s hs0 hj).congr
    hP).congr_right hT

/-- The series part of Lemma 2.1, for the kernel `Riesz1.rieszRepresentative`. For
`s ∈ (0, 1)`:

* the renormalized symmetric partial sums converge at every non-integer point to the kernel.
* the kernel is smooth off the integers, even and periodic.
* on `(0, 1)` it equals `ζ(s, x) + ζ(s, 1 - x)`, with `ζ` the Hurwitz zeta function.
* it is integrable on the circle with mean zero.
* `g_s(x) - |x|^(-s)` extends smoothly across zero on `(-1/2, 1/2)`.
* for every `m ≥ 1` the `m`-th derivatives of the partial sums converge locally uniformly off the
  integers to the `m`-th derivative of the kernel.
* the second derivative is `s (s + 1) ∑ₖ |x - k| ^ (-s - 2)`, which is positive.
* for every `m ≥ 0` the `m`-th derivative is bounded by `C dist(x, 0) ^ (-s - m)` off zero.
* the kernel is bounded below and tends to `+∞` at zero. -/
theorem fundamental_series (s : RieszExponent) :
    (∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      Tendsto (fun M : ℕ => (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s.val)) -
        2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop (𝓝 (rieszRepresentative s x))) ∧
    ContDiffOn ℝ ∞ (fun x : ℝ => rieszRepresentative s x) {x : ℝ | (x : UnitAddCircle) ≠ 0} ∧
    Function.Even (fun x : ℝ => rieszRepresentative s x) ∧
    Function.Periodic (fun x : ℝ => rieszRepresentative s x) 1 ∧
    (∀ x : ℝ, 0 < x → x < 1 →
      rieszRepresentative s x =
        (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (s.val : ℂ)).re +
          (HurwitzZeta.hurwitzZeta ((1 - x : ℝ) : UnitAddCircle) (s.val : ℂ)).re) ∧
    Integrable (fun x : UnitAddCircle => rieszRepresentative s x) ∧
    ∫ x : UnitAddCircle, rieszRepresentative s x = 0 ∧
    (∃ h : ℝ → ℝ, ContDiffOn ℝ ∞ h (Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      ∀ x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2), x ≠ 0 →
        h x = rieszRepresentative s x - |x| ^ (-s.val)) ∧
    (∀ m : ℕ, 1 ≤ m →
      TendstoLocallyUniformlyOn (fun (M : ℕ) (x : ℝ) => iteratedDeriv m (fun y : ℝ =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + y| ^ (-s.val)) -
          2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) x)
        (iteratedDeriv m (fun x : ℝ => rieszRepresentative s x)) atTop
        {x : ℝ | (x : UnitAddCircle) ≠ 0}) ∧
    (∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      iteratedDeriv 2 (fun x : ℝ => rieszRepresentative s x) x =
          s.val * (s.val + 1) * ∑' k : ℤ, |x - k| ^ (-s.val - 2) ∧
        0 < s.val * (s.val + 1) * ∑' k : ℤ, |x - k| ^ (-s.val - 2)) ∧
    (∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      |iteratedDeriv m (fun x : ℝ => rieszRepresentative s x) x| ≤
        C * dist (x : UnitAddCircle) 0 ^ (-s.val - (m : ℝ))) ∧
    (∃ B : ℝ, ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 → B ≤ rieszRepresentative s x) ∧
    Tendsto (fun x : ℝ => rieszRepresentative s x) (𝓝[≠] 0) atTop := by
  have hs0 : 0 < s.val := s.2.1
  have hs1 : s.val < 1 := s.2.2
  refine ⟨fun x hx => tendsto_rieszPartialSum s.val hs0 hs1 x hx,
    contDiffOn_const.mul (contDiffOn_hurwitzZetaEven_re s.val hs0 hs1), ?_, ?_, ?_,
    (integrable_hurwitzZetaEven_re s.val hs0 hs1).const_mul 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact congrArg (fun t : ℝ => 2 * t) (hurwitzZetaEven_re_even (s.val : ℂ) x)
  · intro x
    exact congrArg (fun t : ℝ => 2 * t) (hurwitzZetaEven_re_periodic (s.val : ℂ) x)
  · intro x hx0 hx1
    have h := congrArg Complex.re (hurwitzZetaEven_re_eq_hurwitzZeta_add s.val x)
    simp only [Complex.ofReal_re, Complex.add_re] at h
    show 2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s.val : ℂ)).re = _
    linarith
  · show ∫ x : UnitAddCircle, 2 * (HurwitzZeta.hurwitzZetaEven x (s.val : ℂ)).re = 0
    rw [integral_const_mul, integral_hurwitzZetaEven_re s.val hs0 hs1, mul_zero]
  · obtain ⟨h, hC, hh⟩ := exists_smooth_hurwitzZetaEven_re_remainder s.val hs0 hs1
    exact ⟨h, hC, fun x hx hx0 => hh x hx hx0⟩
  · intro m hm
    exact tendstoLocallyUniformlyOn_partialSum_iteratedDeriv s.val hs0 hs1 hm
  · intro x hx
    have h2 := second_derivative_hurwitzKernel s.val hs0 hs1 x hx
    have hder : iteratedDeriv 2 (hurwitzKernel s.val) x =
        deriv (deriv (hurwitzKernel s.val)) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ⟨hder.trans h2.1.deriv, h2.2.2⟩
  · intro m
    exact iteratedDeriv_hurwitzKernel_bound s.val hs0 hs1 m
  · exact hurwitzZetaEven_re_bounded_below s.val hs0 hs1
  · exact tendsto_hurwitzZetaEven_re_at_zero s.val hs0 hs1

end Riesz1
