/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoDecompositionRadii
public import Riesz1.Variance.VarAlPiecesEnvelopeCompact

/-! # Tails of the separation-free pieces

The normalized radius partition preserves both compact-profile derivative
tails, uniformly in the observation circle. This is the tail part of the
decomposition used in the proof of the second error bound in Theorem 3.
-/

public section

open scoped ContDiff BigOperators

namespace Riesz1.Internal

/-- The explicit normalized pieces inherit a derivative tail. All marks
may coincide. Only their fixed absolute positions enter the tail radius. -/
theorem errorTwo_radii_piece_tail {n : ℕ} (marks : Fin n → ℝ)
    (L h : {r : ℝ // 0 < r}) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {s b A x : ℝ} (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hx : 2 * (2 + ∑ i, |marks i|) ≤ circDist L.val x)
    (hfv : |F x| ≤ A * circDist L.val x ^ (s - 2))
    (hfd : |deriv F x| ≤ A * circDist L.val x ^ (s - 3))
    (j : Fin (n + 1)) :
    |deriv (fun y => F y *
      (Fin.lastCases 1 (fun i => smoothCircleRadius L h (y - marks i)) j) ^ (-1 - b) /
      (1 + ∑ i, smoothCircleRadius L h (y - marks i) ^ (-1 - b))) x| ≤
        A * (1 + 2 * (1 + b) * Real.pi) * circDist L.val x ^ (s - 3) := by
  classical
  let r := circDist L.val x
  have hsum : 0 ≤ ∑ i, |marks i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hr : 0 < r := by dsimp [r]; linarith
  let d : Fin (n + 1) → ℝ → ℝ :=
    Fin.lastCases (fun _ => 1) (fun i y => smoothCircleRadius L h (y - marks i))
  have dlast : d (Fin.last n) = fun _ => 1 := by simp [d]
  have dcast (i : Fin n) : d i.castSucc = fun y => smoothCircleRadius L h (y - marks i) := by
    simp [d]
  have hd (i : Fin (n + 1)) : DifferentiableAt ℝ (d i) x := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [dlast]; exact differentiableAt_const _
    · rw [dcast]
      exact ((contDiff_smoothCircleRadius L h).comp
        (contDiff_id.sub contDiff_const)).differentiable (by simp) x
  have hp (i : Fin (n + 1)) : 0 < d i x := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [dlast]; exact one_pos
    · rw [dcast]; exact smoothCircleRadius_pos L h _
  have hQ : 0 ≤ Real.pi / r := (div_pos Real.pi_pos hr).le
  have hdv (i : Fin (n + 1)) : |deriv (d i) x| ≤ (Real.pi / r) * d i x := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [dlast, deriv_const, abs_zero, mul_one]
      exact hQ
    · rw [dcast]
      have hmk : |marks k| ≤ ∑ i, |marks i| := Finset.single_le_sum
        (f := fun i => |marks i|) (fun i _ => abs_nonneg _) (Finset.mem_univ k)
      have hdist : r ≤ circDist L.val (x - marks k) + |marks k| := by
        simpa only [sub_sub_cancel, abs_neg] using
          circDist_le_add_abs L.property x (x - marks k)
      have hlow := (smoothCircleRadius_comparison L h (x - marks k)).1
      have hrad : r / Real.pi ≤ smoothCircleRadius L h (x - marks k) := by
        have hh : (2 / Real.pi) * circDist L.val (x - marks k) ≤
            smoothCircleRadius L h (x - marks k) :=
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)).trans hlow
        apply (div_le_iff₀ Real.pi_pos).mpr
        have hh' := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
        have he : Real.pi * (2 / Real.pi * circDist L.val (x - marks k)) =
            2 * circDist L.val (x - marks k) := by field_simp
        rw [he] at hh'
        dsimp [r] at *
        nlinarith
      have hrad' : 1 ≤ (Real.pi / r) * smoothCircleRadius L h (x - marks k) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hr).mpr
        have hh := (div_le_iff₀ Real.pi_pos).mp hrad
        convert hh using 1 <;> ring
      have he : deriv (fun y => smoothCircleRadius L h (y - marks k)) x =
          deriv (smoothCircleRadius L h) (x - marks k) :=
        (((contDiff_smoothCircleRadius L h).differentiable (by simp) _).hasDerivAt.comp_sub_const
          x (marks k)).deriv
      rw [he]
      exact (abs_deriv_smoothCircleRadius_le_one L h _).trans hrad'
  have htail := positive_radii_partition_tail_bound
    (hF.differentiable (by simp) x) hd hp (q := 1 + b) (Q := Real.pi / r)
    (by linarith) hQ hdv (by positivity : 0 ≤ A * r ^ (s - 2))
    (by positivity : 0 ≤ A * r ^ (s - 3)) hfv hfd j
  have heq : (fun y => F y * d j y ^ (-(1 + b)) / (∑ k, d k y ^ (-(1 + b)))) =
      fun y => F y *
        (Fin.lastCases 1 (fun i => smoothCircleRadius L h (y - marks i)) j) ^ (-1 - b) /
        (1 + ∑ i, smoothCircleRadius L h (y - marks i) ^ (-1 - b)) := by
    funext y
    rw [show -(1 + b) = -1 - b by ring]
    have he : d j y = Fin.lastCases 1 (fun i => smoothCircleRadius L h (y - marks i)) j := by
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp only [dlast, dcast,
        Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [he]
    congr 1
    rw [Fin.sum_univ_castSucc]
    simp only [dlast, dcast, Real.one_rpow]
    ring
  rw [heq] at htail
  refine htail.trans (le_of_eq ?_)
  have he : r ^ (s - 2) = r ^ (s - 3) * r := by
    calc
      _ = r ^ ((s - 3) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hr, Real.rpow_one]
  rw [he]
  change A * r ^ (s - 3) + 2 * ((1 + b) * (Real.pi / r)) * (A * (r ^ (s - 3) * r)) = _
  field_simp [hr.ne']
  ring

end Riesz1.Internal
