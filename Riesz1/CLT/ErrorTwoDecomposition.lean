/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoDecompositionTails
public import Riesz1.Auxiliary.GradientSplittingZWeights

/-! # Uniform single-center decomposition of the transport derivative

The decomposition in the proof of the second error bound in Theorem 3 is uniform
before the circle length is chosen. Smooth normalized radius weights replace
disjoint cutoffs. Only the fixed number and real positions of the marks
enter the bound. Their circular separation is unrestricted.
-/

public section

open scoped ContDiff BigOperators

namespace Riesz1.Internal

/-- Split any smooth periodic function with the two regularization
envelopes and compact tails into a fixed number of smooth pieces whose
derivatives satisfy the translated a-priori envelopes. Apply this to
the first derivative of the regularized transport. -/
theorem errorTwo_decomposition (n : ℕ) (marks : Fin n → ℝ)
    (s b : ℝ) (hs : s < 3) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L h : {r : ℝ // 0 < r}) (K A : ℝ),
      1 ≤ K → K⁻¹ ≤ h.val → 0 ≤ A →
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → Function.Periodic F L.val →
      (∀ x, |F x| ≤ A * (1 + ∑ j,
        max (circDist L.val (x - marks j)) h.val ^ (-b))) →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
        max (circDist L.val (x - marks j)) h.val ^ (-1 - b))) →
      (∀ x, 2 ≤ circDist L.val x →
        |F x| ≤ A * circDist L.val x ^ (s - 2) ∧
          |deriv F x| ≤ A * circDist L.val x ^ (s - 3)) →
      ∃ φ : Fin (n + 1) → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L.val) ∧
        (∀ x, ∑ j, φ j x = F x) ∧
        (∀ j x, |deriv (φ j) x| ≤ C * A *
          gradWeightTwo s b K L.val (x - Fin.lastCases 0 marks j)) := by
  classical
  obtain ⟨C₀, hC₀, hsplit⟩ := errorTwo_decomposition_radii n b hb
  let R := 2 + ∑ i, |marks i|
  let T := (1 + 2 * (1 + b) * Real.pi) * (2 : ℝ) ^ (3 - s)
  let C := C₀ * (1 + (4 * R) ^ (3 - s)) + T + 1
  have hR : 2 ≤ R := by
    dsimp [R]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (marks i))]
  have hRp : 0 < R := by linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₀C : C₀ ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith : 0 ≤ 4 * R) (3 - s))]
  have hTC : T ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith : 0 ≤ 4 * R) (3 - s))]
  have hRC : C₀ * (4 * R) ^ (3 - s) ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun L h K A hK hh hA F hF hp hfv hfd ht => ?_⟩
  obtain ⟨φ, hφ, hsum, hsing, hback, hform⟩ := hsplit L h marks A hA F hF hp hfv hfd
  have hcenter (j : Fin (n + 1)) : |Fin.lastCases 0 marks j| ≤ R - 2 := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.lastCases_last, abs_zero]
      linarith
    · simp only [Fin.lastCases_castSucc]
      dsimp [R]
      simpa only [add_sub_cancel_left] using
        (Finset.single_le_sum (f := fun i => |marks i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ i))
  have hnear (j : Fin (n + 1)) (x : ℝ)
      (hx : circDist L.val (x - Fin.lastCases 0 marks j) < 1) :
      |deriv (φ j) x| ≤ C₀ * A *
        max (circDist L.val (x - Fin.lastCases 0 marks j)) K⁻¹ ^ (-1 - b) := by
    revert hx
    refine Fin.lastCases ?_ (fun i => ?_) j <;> intro hx
    · simp only [Fin.lastCases_last, sub_zero] at hx ⊢
      exact (hback x).trans (le_mul_of_one_le_right (mul_nonneg hC₀.le hA)
        (one_le_weight_of_lt hx hK (by linarith)))
    · simp only [Fin.lastCases_castSucc] at hx ⊢
      exact (hsing i x).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos
          (lt_max_of_lt_right (inv_pos.mpr (by linarith : 0 < K)))
          (max_le_max le_rfl hh) (by linarith)) (mul_nonneg hC₀.le hA))
  have hglobal (j : Fin (n + 1)) (x : ℝ)
      (hx : 1 ≤ circDist L.val (x - Fin.lastCases 0 marks j)) :
      |deriv (φ j) x| ≤ C₀ * A := by
    revert hx
    refine Fin.lastCases ?_ (fun i => ?_) j <;> intro hx
    · exact hback x
    · simp only [Fin.lastCases_castSucc] at hx
      have hw : max (circDist L.val (x - marks i)) h.val ^ (-1 - b) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (hx.trans (le_max_left _ _)) (by linarith)
      exact (hsing i x).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (mul_nonneg hC₀.le hA))
  have htail (j : Fin (n + 1)) (x : ℝ)
      (hx : 4 * R ≤ circDist L.val (x - Fin.lastCases 0 marks j)) :
      |deriv (φ j) x| ≤ A * T *
        circDist L.val (x - Fin.lastCases 0 marks j) ^ (s - 3) := by
    let z := circDist L.val (x - Fin.lastCases 0 marks j)
    let r := circDist L.val x
    have hdist : z ≤ r + |Fin.lastCases 0 marks j| := by
      simpa only [sub_sub_cancel_left, abs_neg] using
        circDist_le_add_abs L.property (x - Fin.lastCases 0 marks j) x
    have hr : 2 * R ≤ r := by linarith [hcenter j]
    have hz : 0 < z := by dsimp [z]; linarith
    have hzr : z / 2 ≤ r := by linarith [hcenter j]
    have ht' := ht x (by dsimp [r] at hr; linarith)
    have hh' := errorTwo_radii_piece_tail marks L h hF hb hA hr ht'.1 ht'.2 j
    have heq : φ j = fun y => F y *
        (Fin.lastCases 1 (fun i => smoothCircleRadius L h (y - marks i)) j) ^ (-1 - b) /
        (1 + ∑ i, smoothCircleRadius L h (y - marks i) ^ (-1 - b)) := funext (hform j)
    rw [← heq] at hh'
    have hpow : r ^ (s - 3) ≤ 2 ^ (3 - s) * z ^ (s - 3) := by
      calc
        _ ≤ (z / 2) ^ (s - 3) := Real.rpow_le_rpow_of_nonpos (by positivity) hzr (by linarith)
        _ = _ := by
          rw [Real.div_rpow hz.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
            ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show -(s - 3) = 3 - s by ring]
          ring
    exact hh'.trans (by
      have hh'' := mul_le_mul_of_nonneg_left hpow
        (by positivity : 0 ≤ A * (1 + 2 * (1 + b) * Real.pi))
      convert hh'' using 1
      dsimp [T]
      ring)
  refine ⟨φ, hφ, hsum, fun j x => ?_⟩
  let z := circDist L.val (x - Fin.lastCases 0 marks j)
  unfold gradWeightTwo
  split_ifs with hz
  · rw [show -(1 + b) = -1 - b by ring]
    exact (hnear j x hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₀C hA)
      (Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.mpr (by linarith : 0 ≤ K))) _))
  · have hz' : 1 ≤ z := not_lt.mp hz
    simpa only [ite_eq_right hz] using weighted_remainder_bound (W := (1 : ℝ))
      (circDist_nonneg _ _) (by linarith : 2 ≤ 4 * R) hs
      (fun _ => le_rfl) (hglobal j x hz') (htail j x)
      (by nlinarith [mul_le_mul_of_nonneg_right hRC hA])
      (mul_le_mul_of_nonneg_right hC₀C hA)
      (by nlinarith [mul_le_mul_of_nonneg_right hTC hA]) (mul_nonneg hC.le hA)

end Riesz1.Internal
