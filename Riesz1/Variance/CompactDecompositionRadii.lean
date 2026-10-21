/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoDecomposition
public import Riesz1.ToMathlib.PositiveRadiusPartitionValue

/-!
# Both value and derivative bounds for compact radius pieces

Supporting Proposition 5.9. The separation-free partition
of the transport derivative needs both adjacent envelopes and pointwise
domination by the input to control its period-integral corrections.
-/

public section

open scoped ContDiff BigOperators

namespace Riesz1.Internal

/-- The explicit radius partition satisfies the single-center value
bound as well as pointwise domination by the input. -/
theorem compactDecomposition_radius_values (n : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L h : {r : ℝ // 0 < r}) (marks : Fin n → ℝ)
      (A : ℝ), 0 ≤ A → ∀ (F : ℝ → ℝ) (φ : Fin (n + 1) → ℝ → ℝ),
      (∀ x, |F x| ≤ A * (1 + ∑ j,
        max (circDist L.val (x - marks j)) h.val ^ (-b))) →
      (∀ j x, φ j x = F x *
        (Fin.lastCases 1 (fun i => smoothCircleRadius L h (x - marks i)) j) ^ (-1 - b) /
        (1 + ∑ i, smoothCircleRadius L h (x - marks i) ^ (-1 - b))) →
      (∀ (j : Fin n) x, |φ j.castSucc x| ≤ C * A *
        max (circDist L.val (x - marks j)) h.val ^ (-b)) ∧
      (∀ x, |φ (Fin.last n) x| ≤ C * A) ∧
      (∀ j x, |φ j x| ≤ |F x|) := by
  classical
  let B : ℝ := 2 ^ b
  let E : ℝ := (Real.pi / 2) ^ b
  let m : ℝ := ((n + 1 : ℕ) : ℝ)
  let C := B * m * E
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := Real.one_le_rpow (by norm_num) hb
  have hE : 0 < E := by dsimp [E]; positivity
  have hE1 : 1 ≤ E := Real.one_le_rpow (by nlinarith [Real.two_le_pi]) hb
  refine ⟨C, by dsimp [C, m]; positivity, fun L h marks A hA F φ hval hform => ?_⟩
  let d : Fin (n + 1) → ℝ → ℝ :=
    Fin.lastCases (fun _ => 1) (fun j x => smoothCircleRadius L h (x - marks j))
  have dlast : d (Fin.last n) = fun _ => 1 := by simp [d]
  have dcast (i : Fin n) : d i.castSucc = fun x => smoothCircleRadius L h (x - marks i) := by
    simp [d]
  have hp (j : Fin (n + 1)) (x : ℝ) : 0 < d j x := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [dlast]; exact one_pos
    · rw [dcast]; exact smoothCircleRadius_pos L h _
  have heq (j : Fin (n + 1)) (x : ℝ) : φ j x =
      F x * d j x ^ (-1 - b) / (∑ k, d k x ^ (-1 - b)) := by
    rw [hform]
    have hd : d j x = Fin.lastCases 1 (fun i => smoothCircleRadius L h (x - marks i)) j := by
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp only [dlast, dcast,
        Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [hd, Fin.sum_univ_castSucc]
    simp only [dlast, dcast, Real.one_rpow]
    congr 1
    ring
  have hval' (x : ℝ) : |F x| ≤ (A * B) * ∑ j, d j x ^ (-b) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      (errorTwo_radius_power_comparison L h hb (x - marks j)).1)
    rw [← Finset.mul_sum] at hh
    have hh' : 1 + ∑ j, max (circDist L.val (x - marks j)) h.val ^ (-b) ≤
        B * (∑ j, d j x ^ (-b)) := by
      rw [Fin.sum_univ_castSucc, dlast, Real.one_rpow, mul_add, mul_one]
      simp only [dcast]
      dsimp [B] at *
      linarith
    exact (hval x).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh' hA)
  have hv (j : Fin (n + 1)) (x : ℝ) :
      |φ j x| ≤ A * B * m * d j x ^ (-b) := by
    rw [heq]
    simpa only [Fintype.card_fin] using positive_radii_partition_value_bound
      (fun j => d j x) (fun j => hp j x) (mul_nonneg hA hB.le) hb (hval' x) j
  refine ⟨fun j x => ?_, fun x => ?_, fun j x => ?_⟩
  · have hh := (hv j.castSucc x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dcast] using (errorTwo_radius_power_comparison L h hb (x - marks j)).2)
      (by positivity : 0 ≤ A * B * m))
    convert hh using 1
    dsimp [C, E]
    ring
  · have hh := hv (Fin.last n) x
    rw [dlast, Real.one_rpow, mul_one] at hh
    have hh' := hh.trans (le_mul_of_one_le_right (by positivity : 0 ≤ A * B * m) hE1)
    convert hh' using 1
    dsimp [C]
    ring
  · rw [heq]
    exact abs_positive_radii_partition_le (fun j => d j x) (fun j => hp j x) (F x) b j

end Riesz1.Internal
