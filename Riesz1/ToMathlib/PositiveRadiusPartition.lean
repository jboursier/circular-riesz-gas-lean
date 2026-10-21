/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

/-!
# Partitions using positive radii

Normalized negative powers of positive radii split a function with finitely
many power singularities. The derivative estimate uses no separation between
the radii's centers. This is useful when marked points on a varying circle
can approach one another.
-/

public section

open scoped ContDiff BigOperators

namespace Riesz1

/-- A finite nonempty family of positive radii has a positive minimum. -/
theorem positive_radii_minimum {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) (hd : ∀ j, 0 < d j) :
    ∃ j, 0 < d j ∧ ∀ k, d j ≤ d k := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  exact ⟨j, hd j, fun k => hj k (Finset.mem_univ k)⟩

/-- The two adjacent power sums are controlled by the smallest radius.
The cardinality factor is uniform even when several radii coincide. -/
theorem positive_radii_power_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) (hd : ∀ j, 0 < d j) {b : ℝ} (hb : 0 ≤ b)
    (i : ι) (hi : ∀ j, d i ≤ d j) :
    (∑ j, d j ^ (-b)) ≤
      (Fintype.card ι : ℝ) * d i * ∑ j, d j ^ (-1 - b) := by
  classical
  have hpow : d i ^ (-b) = d i * d i ^ (-1 - b) := by
    calc
      _ = d i ^ ((1 : ℝ) + (-1 - b)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add (hd i), Real.rpow_one]
  have hterm (j : ι) : d j ^ (-b) ≤ d i * ∑ k, d k ^ (-1 - b) := by
    calc
      d j ^ (-b) ≤ d i ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos (hd i) (hi j) (by linarith)
      _ = d i * d i ^ (-1 - b) := hpow
      _ ≤ d i * ∑ k, d k ^ (-1 - b) := mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun k _ => Real.rpow_nonneg (hd k).le _)
          (Finset.mem_univ i)) (hd i).le
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hs

/-- Quotient differentiation with scale-aware bounds. The numerator need
not be positive. -/
theorem abs_deriv_weighted_quotient_le
    {f w S : ℝ → ℝ} {x A n q r : ℝ}
    (hf : DifferentiableAt ℝ f x) (hw : DifferentiableAt ℝ w x)
    (hS : DifferentiableAt ℝ S x) (hSp : 0 < S x) (hr : 0 < r)
    (hA : 0 ≤ A) (hn : 0 ≤ n) (_hq : 0 ≤ q) (hwp : 0 ≤ w x)
    (hfv : |f x| ≤ A * n * r * S x)
    (hfd : |deriv f x| ≤ A * S x)
    (hwd : |deriv w x| ≤ q * w x / r)
    (hSd : |deriv S x| ≤ q * S x / r) :
    |deriv (fun y => f y * w y / S y) x| ≤
      A * (1 + 2 * n * q) * w x := by
  change |deriv (f * w / S) x| ≤ _
  rw [deriv_div (hf.mul hw) hS hSp.ne', deriv_mul hf hw, abs_div,
    abs_of_pos (sq_pos_of_pos hSp)]
  have hnum : |(deriv f x * w x + f x * deriv w x) * S x -
      (f x * w x) * deriv S x| ≤
      ((A * S x) * w x + (A * n * r * S x) * (q * w x / r)) * S x +
        ((A * n * r * S x) * w x) * (q * S x / r) := by
    have h1 : |deriv f x * w x| ≤ (A * S x) * w x := by
      rw [abs_mul, abs_of_nonneg hwp]
      exact mul_le_mul_of_nonneg_right hfd hwp
    have h2 : |f x * deriv w x| ≤ (A * n * r * S x) * (q * w x / r) := by
      rw [abs_mul]
      exact mul_le_mul hfv hwd (abs_nonneg _) (by positivity)
    have h3 : |(f x * w x) * deriv S x| ≤
        ((A * n * r * S x) * w x) * (q * S x / r) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hwp]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hfv hwp) hSd
        (abs_nonneg _) (by positivity)
    calc
      _ ≤ |(deriv f x * w x + f x * deriv w x) * S x| +
          |(f x * w x) * deriv S x| := abs_sub _ _
      _ ≤ (|deriv f x * w x| + |f x * deriv w x|) * S x +
          |(f x * w x) * deriv S x| := by
        rw [abs_mul, abs_of_pos hSp]
        exact add_le_add (mul_le_mul_of_nonneg_right (abs_add_le _ _) hSp.le) le_rfl
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (add_le_add h1 h2) hSp.le) h3
  apply (div_le_iff₀ (sq_pos_of_pos hSp)).mpr
  calc
    _ ≤ _ := hnum
    _ = A * (1 + 2 * n * q) * w x * S x ^ 2 := by field_simp; ring

/-- A separation-free partition estimate. If `f` and its derivative have
the adjacent negative-power envelopes for smooth positive radii with
derivatives at most one, then each normalized piece has a single-radius
derivative envelope. No distance between different centers occurs. -/
theorem positive_radii_partition_deriv_bound
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ℝ → ℝ} {d : ι → ℝ → ℝ} {x A b : ℝ}
    (hf : DifferentiableAt ℝ f x)
    (hd : ∀ j, DifferentiableAt ℝ (d j) x)
    (hp : ∀ j, 0 < d j x) (hdv : ∀ j, |deriv (d j) x| ≤ 1)
    (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hfv : |f x| ≤ A * (∑ j, d j x ^ (-b)))
    (hfd : |deriv f x| ≤ A * (∑ j, d j x ^ (-1 - b))) (j : ι) :
    |deriv (fun y => f y * d j y ^ (-1 - b) /
      (∑ k, d k y ^ (-1 - b))) x| ≤
        A * (1 + 2 * (Fintype.card ι : ℝ) * (1 + b)) * d j x ^ (-1 - b) := by
  classical
  let w : ι → ℝ → ℝ := fun k y => d k y ^ (-1 - b)
  let S : ℝ → ℝ := fun y => ∑ k, w k y
  have hw (k : ι) : HasDerivAt (w k)
      ((-1 - b) * d k x ^ (-1 - b - 1) * deriv (d k) x) x := by
    convert (hd k).hasDerivAt.rpow_const (p := -1 - b) (Or.inl (hp k).ne') using 1
    ring
  have hS : HasDerivAt S
      (∑ k, (-1 - b) * d k x ^ (-1 - b - 1) * deriv (d k) x) x :=
    HasDerivAt.fun_sum fun k _ => hw k
  have hwpos (k : ι) : 0 < w k x := Real.rpow_pos_of_pos (hp k) _
  have hSp : 0 < S x := Finset.sum_pos (fun k _ => hwpos k) Finset.univ_nonempty
  obtain ⟨i, hi, hmin⟩ := positive_radii_minimum (fun k => d k x) hp
  have hwd (k : ι) : |deriv (w k) x| ≤ (1 + b) * w k x / d i x := by
    rw [(hw k).deriv, abs_mul, abs_mul, abs_of_nonpos (by linarith : -1 - b ≤ 0),
      abs_of_pos (Real.rpow_pos_of_pos (hp k) _)]
    have he : d k x ^ (-1 - b - 1) = w k x / d k x := by
      dsimp [w]
      rw [Real.rpow_sub (hp k), Real.rpow_one]
    rw [he]
    rw [show -(-1 - b) = 1 + b by ring]
    calc
      _ ≤ (1 + b) * (w k x / d k x) * 1 := by
        apply mul_le_mul_of_nonneg_left (hdv k)
        exact mul_nonneg (by linarith) (div_nonneg (hwpos k).le (hp k).le)
      _ ≤ (1 + b) * w k x / d i x := by
        rw [mul_one, ← mul_div_assoc]
        exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (hwpos k).le) hi (hmin k)
  have hSd : |deriv S x| ≤ (1 + b) * S x / d i x := by
    rw [hS.deriv]
    calc
      _ ≤ ∑ k, |deriv (w k) x| := by
        simpa only [(hw _).deriv] using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (f := fun k => (-1 - b) * d k x ^ (-1 - b - 1) * deriv (d k) x))
      _ ≤ ∑ k, (1 + b) * w k x / d i x := Finset.sum_le_sum fun k _ => hwd k
      _ = (1 + b) * S x / d i x := by rw [← Finset.sum_div, ← Finset.mul_sum]
  have hfv' : |f x| ≤ A * (Fintype.card ι : ℝ) * d i x * S x := by
    calc
      _ ≤ A * ((Fintype.card ι : ℝ) * d i x * S x) :=
        hfv.trans (mul_le_mul_of_nonneg_left
          (positive_radii_power_sum (fun k => d k x) hp hb i hmin) hA)
      _ = _ := by ring
  exact abs_deriv_weighted_quotient_le hf (hw j).differentiableAt hS.differentiableAt
    hSp hi hA (Nat.cast_nonneg _) (by linarith) (hwpos j).le hfv' hfd (hwd j) hSd

/-- The normalized pieces add to the original function wherever the radii
are positive. This includes coincident radii and a singleton family. -/
theorem sum_positive_radii_partition {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ℝ → ℝ) (d : ι → ℝ → ℝ) (b x : ℝ) (hp : ∀ j, 0 < d j x) :
    (∑ j, f x * d j x ^ (-1 - b) / (∑ k, d k x ^ (-1 - b))) = f x := by
  classical
  have hS : 0 < ∑ k, d k x ^ (-1 - b) :=
    Finset.sum_pos (fun k _ => Real.rpow_pos_of_pos (hp k) _) Finset.univ_nonempty
  rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_cancel_right₀ _ hS.ne']

/-- Smooth periodic radii produce smooth periodic pieces, with an exact
sum and the same uniform single-radius bound. The formula is explicit.
There is no choice of a partition or separation parameter. -/
theorem positive_radii_partition
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ℝ → ℝ} {d : ι → ℝ → ℝ} {L A b : ℝ}
    (hf : ContDiff ℝ ∞ f) (hfp : Function.Periodic f L)
    (hd : ∀ j, ContDiff ℝ ∞ (d j))
    (hdp : ∀ j, Function.Periodic (d j) L)
    (hp : ∀ j x, 0 < d j x) (hdv : ∀ j x, |deriv (d j) x| ≤ 1)
    (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hfv : ∀ x, |f x| ≤ A * (∑ j, d j x ^ (-b)))
    (hfd : ∀ x, |deriv f x| ≤ A * (∑ j, d j x ^ (-1 - b))) :
    ∃ φ : ι → ℝ → ℝ,
      (∀ j x, φ j x = f x * d j x ^ (-1 - b) /
        (∑ k, d k x ^ (-1 - b))) ∧
      (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L) ∧
      (∀ x, ∑ j, φ j x = f x) ∧
      (∀ j x, |deriv (φ j) x| ≤
        A * (1 + 2 * (Fintype.card ι : ℝ) * (1 + b)) * d j x ^ (-1 - b)) := by
  classical
  let w : ι → ℝ → ℝ := fun j x => d j x ^ (-1 - b)
  have hw (j : ι) : ContDiff ℝ ∞ (w j) :=
    (hd j).rpow_const_of_ne (fun x => (hp j x).ne')
  have hS (x : ℝ) : (∑ j, w j x) ≠ 0 := ne_of_gt
    (Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hp j x) _) Finset.univ_nonempty)
  refine ⟨fun j x => f x * w j x / (∑ k, w k x), fun _ _ => rfl,
    fun j => ⟨(hf.mul (hw j)).div (ContDiff.sum fun k _ => hw k) hS, ?_⟩,
    fun x => sum_positive_radii_partition f d b x (fun j => hp j x), ?_⟩
  · intro x
    simp only [w, hfp x, hdp _ x]
  · intro j x
    exact positive_radii_partition_deriv_bound (hf.differentiable (by simp) x)
      (fun k => (hd k).differentiable (by simp) x) (fun k => hp k x)
      (fun k => hdv k x) hA hb (hfv x) (hfd x) j

/-- A normalized weight preserves polynomial tails if its logarithmic
derivative and that of the denominator decay inversely with distance. -/
theorem abs_deriv_normalized_piece_le
    {f w S : ℝ → ℝ} {x F₀ F₁ Q : ℝ}
    (hf : DifferentiableAt ℝ f x) (hw : DifferentiableAt ℝ w x)
    (hS : DifferentiableAt ℝ S x) (hSp : 0 < S x)
    (hwp : 0 ≤ w x) (hwS : w x ≤ S x)
    (hF₀ : 0 ≤ F₀) (hF₁ : 0 ≤ F₁) (hQ : 0 ≤ Q)
    (hfv : |f x| ≤ F₀) (hfd : |deriv f x| ≤ F₁)
    (hwd : |deriv w x| ≤ Q * w x) (hSd : |deriv S x| ≤ Q * S x) :
    |deriv (fun y => f y * w y / S y) x| ≤ F₁ + 2 * Q * F₀ := by
  change |deriv (f * w / S) x| ≤ _
  rw [deriv_div (hf.mul hw) hS hSp.ne', deriv_mul hf hw, abs_div,
    abs_of_pos (sq_pos_of_pos hSp)]
  apply (div_le_iff₀ (sq_pos_of_pos hSp)).mpr
  have h1 : |deriv f x * w x| ≤ F₁ * w x := by
    rw [abs_mul, abs_of_nonneg hwp]
    exact mul_le_mul_of_nonneg_right hfd hwp
  have h2 : |f x * deriv w x| ≤ F₀ * (Q * w x) := by
    rw [abs_mul]
    exact mul_le_mul hfv hwd (abs_nonneg _) hF₀
  have h3 : |f x * w x * deriv S x| ≤ (F₀ * w x) * (Q * S x) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hwp]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hfv hwp) hSd (abs_nonneg _)
      (mul_nonneg hF₀ hwp)
  calc
    _ ≤ |(deriv f x * w x + f x * deriv w x) * S x| +
        |f x * w x * deriv S x| := abs_sub _ _
    _ ≤ (|deriv f x * w x| + |f x * deriv w x|) * S x +
        |f x * w x * deriv S x| := by
      rw [abs_mul, abs_of_pos hSp]
      exact add_le_add (mul_le_mul_of_nonneg_right (abs_add_le _ _) hSp.le) le_rfl
    _ ≤ (F₁ * w x + F₀ * (Q * w x)) * S x + (F₀ * w x) * (Q * S x) :=
      add_le_add (mul_le_mul_of_nonneg_right (add_le_add h1 h2) hSp.le) h3
    _ = (F₁ + 2 * Q * F₀) * w x * S x := by ring
    _ ≤ (F₁ + 2 * Q * F₀) * S x ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hwS
        (mul_nonneg (by positivity : 0 ≤ F₁ + 2 * Q * F₀) hSp.le)]

/-- A logarithmic derivative bound for a positive radius gives the
corresponding bound for its negative power. -/
theorem abs_deriv_negative_power_le {d : ℝ → ℝ} {x q Q : ℝ}
    (hd : DifferentiableAt ℝ d x) (hp : 0 < d x) (hq : 0 ≤ q)
    (_hQ : 0 ≤ Q) (hder : |deriv d x| ≤ Q * d x) :
    |deriv (fun y => d y ^ (-q)) x| ≤ q * Q * d x ^ (-q) := by
  rw [(hd.hasDerivAt.rpow_const (p := -q) (Or.inl hp.ne')).deriv,
    abs_mul, abs_mul, abs_neg, abs_of_nonneg hq,
    abs_of_pos (Real.rpow_pos_of_pos hp _)]
  have he : d x ^ (-q - 1) = d x ^ (-q) / d x := by
    rw [Real.rpow_sub hp, Real.rpow_one]
  rw [he]
  calc
    _ ≤ Q * d x * q * (d x ^ (-q) / d x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hder hq) (by positivity)
    _ = _ := by field_simp [hp.ne']

/-- Tail bounds for normalized negative-power pieces. The radii only
need a common logarithmic derivative bound at the point in question. -/
theorem positive_radii_partition_tail_bound
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ℝ → ℝ} {d : ι → ℝ → ℝ} {x q Q F₀ F₁ : ℝ}
    (hf : DifferentiableAt ℝ f x)
    (hd : ∀ j, DifferentiableAt ℝ (d j) x) (hp : ∀ j, 0 < d j x)
    (hq : 0 ≤ q) (hQ : 0 ≤ Q)
    (hdv : ∀ j, |deriv (d j) x| ≤ Q * d j x)
    (hF₀ : 0 ≤ F₀) (hF₁ : 0 ≤ F₁)
    (hfv : |f x| ≤ F₀) (hfd : |deriv f x| ≤ F₁) (j : ι) :
    |deriv (fun y => f y * d j y ^ (-q) / (∑ k, d k y ^ (-q))) x| ≤
      F₁ + 2 * (q * Q) * F₀ := by
  classical
  let w : ι → ℝ → ℝ := fun j y => d j y ^ (-q)
  let S : ℝ → ℝ := fun y => ∑ k, w k y
  have hw (j : ι) : DifferentiableAt ℝ (w j) x :=
    ((hd j).hasDerivAt.rpow_const (p := -q) (Or.inl (hp j).ne')).differentiableAt
  have hS : DifferentiableAt ℝ S x := DifferentiableAt.fun_sum fun k _ => hw k
  have hwp (k : ι) : 0 < w k x := Real.rpow_pos_of_pos (hp k) _
  have hSp : 0 < S x := Finset.sum_pos (fun k _ => hwp k) Finset.univ_nonempty
  have hwd (k : ι) : |deriv (w k) x| ≤ q * Q * w k x :=
    abs_deriv_negative_power_le (hd k) (hp k) hq hQ (hdv k)
  have hSd : |deriv S x| ≤ q * Q * S x := by
    rw [show deriv S x = ∑ k, deriv (w k) x from
      (HasDerivAt.fun_sum fun k _ => (hw k).hasDerivAt).deriv]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc
        _ ≤ ∑ k, q * Q * w k x := Finset.sum_le_sum fun k _ => hwd k
        _ = _ := (Finset.mul_sum _ _ _).symm)
  exact abs_deriv_normalized_piece_le hf (hw j) hS hSp (hwp j).le
    (Finset.single_le_sum (fun k _ => (hwp k).le) (Finset.mem_univ j))
    hF₀ hF₁ (mul_nonneg hq hQ) hfv hfd (hwd j) hSd

end Riesz1
