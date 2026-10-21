/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.CompactDecompositionRadii

/-!
# Compact derivative pieces with both transport envelopes

Proposition 5.9: a separation-free analytic partition of a
transport derivative, before correcting its period integrals. The two
adjacent envelopes and domination by the derivative are retained.
-/

public section

open scoped ContDiff BigOperators

namespace Riesz1.Internal

/-- Split a smooth compact-envelope function into smooth periodic pieces,
retaining both single-center envelopes and pointwise domination. -/
theorem compactDecomposition_partition (n : ℕ) (marks : Fin n → ℝ)
    (s b : ℝ) (hs : s < 1) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L h : {r : ℝ // 0 < r}) (K A : ℝ),
      1 ≤ K → K⁻¹ ≤ h.val → 0 ≤ A →
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → Function.Periodic F L.val →
      (∀ x, |F x| ≤ A * (1 + ∑ j,
        max (circDist L.val (x - marks j)) h.val ^ (-b))) →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
        max (circDist L.val (x - marks j)) h.val ^ (-1 - b))) →
      (∀ x, 4 ≤ circDist L.val x →
        |F x| ≤ A * circDist L.val x ^ (s - 2) ∧
          |deriv F x| ≤ A * circDist L.val x ^ (s - 3)) →
      ∃ φ : Fin (n + 1) → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L.val) ∧
        (∀ x, ∑ j, φ j x = F x) ∧
        (∀ j x,
          |φ j x| ≤ C * A * gradWeightOne s b K L.val (x - Fin.lastCases 0 marks j) ∧
          |deriv (φ j) x| ≤ C * A * gradWeightTwo s b K L.val (x - Fin.lastCases 0 marks j)) ∧
        (∀ j x, |φ j x| ≤ |F x|) := by
  classical
  obtain ⟨C₀, hC₀, hsplit⟩ := errorTwo_decomposition_radii n b hb
  obtain ⟨V, hV, hvalues⟩ := compactDecomposition_radius_values n hb
  let R := 2 + ∑ i, |marks i|
  let T := (1 + 2 * (1 + b) * Real.pi) * (2 : ℝ) ^ (3 - s)
  let U := (2 : ℝ) ^ (2 - s)
  let C := (C₀ + V) * (1 + (4 * R) ^ (3 - s) + (4 * R) ^ (2 - s)) + T + U + 1
  have hR : 2 ≤ R := by
    dsimp [R]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (marks i))]
  have hRp : 0 < R := by linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hbase : C₀ + V ≤ (C₀ + V) *
      (1 + (4 * R) ^ (3 - s) + (4 * R) ^ (2 - s)) :=
    le_mul_of_one_le_right (by positivity) (by
      linarith [Real.rpow_nonneg (by positivity : 0 ≤ 4 * R) (3 - s),
        Real.rpow_nonneg (by positivity : 0 ≤ 4 * R) (2 - s)])
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith
  have hTC : T ≤ C := by dsimp [C]; linarith
  have hRC : C₀ * (4 * R) ^ (3 - s) ≤ C := by
    dsimp [C]
    nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ 4 * R) (3 - s),
      Real.rpow_nonneg (by positivity : 0 ≤ 4 * R) (2 - s)]
  have hVC : V ≤ C := by dsimp [C]; linarith
  have hUC : U ≤ C := by dsimp [C]; linarith
  have hRVC : V * (4 * R) ^ (2 - s) ≤ C := by
    dsimp [C]
    nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ 4 * R) (3 - s),
      Real.rpow_nonneg (by positivity : 0 ≤ 4 * R) (2 - s)]
  refine ⟨C, hC, fun L h K A hK hh hA F hF hp hfv hfd ht => ?_⟩
  obtain ⟨φ, hφ, hsum, hsing, hback, hform⟩ := hsplit L h marks A hA F hF hp hfv hfd
  obtain ⟨hsv, hbv, hdom⟩ := hvalues L h marks A hA F φ hfv hform
  have hcenter (j : Fin (n + 1)) : |Fin.lastCases 0 marks j| ≤ R - 2 := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.lastCases_last, abs_zero]
      linarith
    · simp only [Fin.lastCases_castSucc]
      dsimp [R]
      simpa only [add_sub_cancel_left] using
        (Finset.single_le_sum (f := fun i => |marks i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ i))
  have hneard (j : Fin (n + 1)) (x : ℝ)
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
  have hglobald (j : Fin (n + 1)) (x : ℝ)
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
  have htaild (j : Fin (n + 1)) (x : ℝ)
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
  have hnearv (j : Fin (n + 1)) (x : ℝ)
      (hx : circDist L.val (x - Fin.lastCases 0 marks j) < 1) :
      |φ j x| ≤ V * A * max (circDist L.val (x - Fin.lastCases 0 marks j)) K⁻¹ ^ (-b) := by
    revert hx
    refine Fin.lastCases ?_ (fun i => ?_) j <;> intro hx
    · simp only [Fin.lastCases_last, sub_zero] at hx ⊢
      exact (hbv x).trans (le_mul_of_one_le_right (mul_nonneg hV.le hA)
        (one_le_weight_of_lt hx hK (by linarith)))
    · simp only [Fin.lastCases_castSucc] at hx ⊢
      exact (hsv i x).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos
          (lt_max_of_lt_right (inv_pos.mpr (by linarith : 0 < K)))
          (max_le_max le_rfl hh) (by linarith)) (mul_nonneg hV.le hA))
  have hglobalv (j : Fin (n + 1)) (x : ℝ)
      (hx : 1 ≤ circDist L.val (x - Fin.lastCases 0 marks j)) : |φ j x| ≤ V * A := by
    revert hx
    refine Fin.lastCases ?_ (fun i => ?_) j <;> intro hx
    · exact hbv x
    · simp only [Fin.lastCases_castSucc] at hx
      exact (hsv i x).trans (by
        have hw := Real.rpow_le_one_of_one_le_of_nonpos (hx.trans (le_max_left _ h.val))
          (by linarith : -b ≤ 0)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (mul_nonneg hV.le hA))
  have htailv (j : Fin (n + 1)) (x : ℝ)
      (hx : 4 * R ≤ circDist L.val (x - Fin.lastCases 0 marks j)) :
      |φ j x| ≤ A * U * circDist L.val (x - Fin.lastCases 0 marks j) ^ (s - 2) := by
    let z := circDist L.val (x - Fin.lastCases 0 marks j)
    let r := circDist L.val x
    have hdist : z ≤ r + |Fin.lastCases 0 marks j| := by
      simpa only [sub_sub_cancel_left, abs_neg] using
        circDist_le_add_abs L.property (x - Fin.lastCases 0 marks j) x
    have hr : 2 * R ≤ r := by linarith [hcenter j]
    have hz : 0 < z := by dsimp [z]; linarith
    have hzr : z / 2 ≤ r := by linarith [hcenter j]
    have hpow : r ^ (s - 2) ≤ U * z ^ (s - 2) := by
      calc
        _ ≤ (z / 2) ^ (s - 2) := Real.rpow_le_rpow_of_nonpos (by positivity) hzr (by linarith)
        _ = _ := by
          rw [Real.div_rpow hz.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
            ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show -(s - 2) = 2 - s by ring]
          dsimp [U]
          ring
    exact (hdom j x).trans (((ht x (by dsimp [r] at hr; linarith)).1).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hA))
  refine ⟨φ, hφ, hsum, fun j x => ⟨?_, ?_⟩, hdom⟩
  · unfold gradWeightOne
    split_ifs with hz
    · exact (hnearv j x hz).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hVC hA) (by positivity))
    · exact weighted_remainder_bound (circDist_nonneg _ _) (by linarith : 2 ≤ 4 * R)
        (by linarith : s < 2) (W := (1 : ℝ)) (fun _ => le_rfl)
        (hglobalv j x (not_lt.mp hz)) (htailv j x)
        (by nlinarith [mul_le_mul_of_nonneg_right hRVC hA])
        (mul_le_mul_of_nonneg_right hVC hA)
        (by nlinarith [mul_le_mul_of_nonneg_right hUC hA]) (mul_nonneg hC.le hA)
        |>.trans (le_of_eq (by simp only [ite_eq_right hz]))
  · unfold gradWeightTwo
    split_ifs with hz
    · rw [show -(1 + b) = -1 - b by ring]
      exact (hneard j x hz).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₀C hA) (by positivity))
    · simpa only [ite_eq_right hz] using weighted_remainder_bound (W := (1 : ℝ))
        (circDist_nonneg _ _) (by linarith : 2 ≤ 4 * R) (by linarith : s < 3)
        (fun _ => le_rfl) (hglobald j x (not_lt.mp hz)) (htaild j x)
        (by nlinarith [mul_le_mul_of_nonneg_right hRC hA])
        (mul_le_mul_of_nonneg_right hC₀C hA)
        (by nlinarith [mul_le_mul_of_nonneg_right hTC hA]) (mul_nonneg hC.le hA)

end Riesz1.Internal
