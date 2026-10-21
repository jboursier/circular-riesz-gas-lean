/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.TransportRegularity

/-!
# Increasing the profile exponent at the exceptional exponents

The endpoint step of Lemma 5.3 uses the original
transport with a slightly larger exponent. The same transport witnesses
the regularity predicate with an explicit envelope factor depending
only on the marks and the exponent increase, uniformly in the circle length.
The tail envelope is retained.
-/

public section

open MeasureTheory

namespace Riesz1.Internal

/-- Increasing the singularity exponent preserves the actual
transport regularity, with a quantitative factor independent of the test
and the circle length. -/
theorem transportRegularity_increase_exponent (P : Parameters) (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (n : ℕ+) (a : Fin (n : ℕ) → ℝ) {α α' C₀ : ℝ}
    (hα : α ≤ α') (hC₀ : 0 ≤ C₀)
    (hreg : TransportRegularity P L f n a α C₀) :
    TransportRegularity P L f n a α'
      (C₀ * (1 + ∑ j, |a j|) ^ (α'-α)) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  rcases hreg with ⟨hinj, ψ, hcoeff, hpoint⟩
  refine ⟨hinj, ψ, hcoeff, fun x hx => ?_⟩
  refine ⟨(hpoint x hx).1, (hpoint x hx).2.trans ?_⟩
  let R := 1 + ∑ j, |a j|
  let D := R ^ (α'-α)
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun j _ => abs_nonneg (a j))]
  have hR0 : 0 < R := by linarith
  have hD : 1 ≤ D := Real.one_le_rpow hR (sub_nonneg.mpr hα)
  have hsingle (j : Fin (n : ℕ)) (hx0 : dist (x : Circle L) 0 ≤ 1) :
      dist (x : Circle L) (a j : Circle L) ^ (-2+P.val.2-α) ≤
        D * dist (x : Circle L) (a j : Circle L) ^ (-2+P.val.2-α') := by
    have hd0 : 0 < dist (x : Circle L) (a j : Circle L) := dist_pos.mpr (hx j)
    have hdR : dist (x : Circle L) (a j : Circle L) ≤ R := by
      have ha : dist (a j : Circle L) 0 ≤ |a j| := by
        rw [dist_zero_right]
        exact QuotientAddGroup.norm_mk_le_norm
      have hasum := Finset.single_le_sum (s := Finset.univ) (f := fun j => |a j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      have ht := dist_triangle (x : Circle L) 0 (a j : Circle L)
      rw [dist_comm (0 : Circle L)] at ht
      dsimp [R]
      linarith
    have he : -2+P.val.2-α = (-2+P.val.2-α')+(α'-α) := by ring
    rw [he, Real.rpow_add hd0]
    calc
      _ ≤ dist (x : Circle L) (a j : Circle L) ^ (-2+P.val.2-α') * D :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hd0.le hdR (sub_nonneg.mpr hα))
          (Real.rpow_nonneg dist_nonneg _)
      _ = _ := mul_comm _ _
  have hnear :
      (if dist (x : Circle L) 0 ≤ 1 then
        ∑ j, dist (x : Circle L) (a j : Circle L) ^ (-2+P.val.2-α) else 0) ≤
      D * (if dist (x : Circle L) 0 ≤ 1 then
        ∑ j, dist (x : Circle L) (a j : Circle L) ^ (-2+P.val.2-α') else 0) := by
    split_ifs with hx0
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => hsingle j hx0)
    · simp
  have htail : 0 ≤ (if 1 ≤ dist (x : Circle L) 0 then
      dist (x : Circle L) 0 ^ (-3+P.val.2) else 0) := by
    split_ifs <;> positivity
  have ht : (if 1 ≤ dist (x : Circle L) 0 then
      dist (x : Circle L) 0 ^ (-3+P.val.2) else 0) ≤
      D * (if 1 ≤ dist (x : Circle L) 0 then
      dist (x : Circle L) 0 ^ (-3+P.val.2) else 0) :=
    le_mul_of_one_le_left htail hD
  have hboth := add_le_add hnear ht
  rw [← mul_add] at hboth
  exact (mul_le_mul_of_nonneg_left hboth hC₀).trans_eq (by
    dsimp [D, R]
    ring)

end Riesz1.Internal
