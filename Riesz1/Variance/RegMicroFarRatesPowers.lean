/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Transition powers and exponent loss in microscopic variance

Scalar estimates in Lemma 5.3, including endpoint
exponent replacement and the absorption of bounded microscopic lengths.
-/

public section

namespace Riesz1.Internal

/-- The moving-cutoff derivative times its transition value has the
same power as the kernel derivative, with a factor independent of `h`. -/
theorem regMicro_transition_power {h r s α : ℝ}
    (hh : 0 < h) (hr : 0 < r) (hrh : r ≤ 4*h) (hq : 0 ≤ 2-s+α) :
    h⁻¹*h^(-α) ≤ 4^(2-s+α)*h^(1-s)*r^(-2+s-α) := by
  have hp : (4*h)^(-2+s-α) ≤ r^(-2+s-α) :=
    Real.rpow_le_rpow_of_nonpos hr hrh (by linarith)
  have hid : 4^(2-s+α)*h^(1-s)*(4*h)^(-2+s-α) = h⁻¹*h^(-α) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hh.le]
    calc
      _ = (4^(2-s+α)*4^(-2+s-α))*(h^(1-s)*h^(-2+s-α)) := by ring
      _ = h^(-1-α) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4),
          ← Real.rpow_add hh, show (2-s+α)+(-2+s-α) = 0 by ring,
          show (1-s)+(-2+s-α) = -1-α by ring, Real.rpow_zero, one_mul]
      _ = h^(-1 : ℝ)*h^(-α) := by rw [← Real.rpow_add hh]; congr 1
      _ = _ := by rw [Real.rpow_neg_one]
  exact hid.symm.trans_le (mul_le_mul_of_nonneg_left hp (by positivity))

/-- A fixed-cutoff value of order `h` is also of order `h^(1-s)`. -/
theorem regMicro_fixed_value_power {h s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hs : 0 ≤ s) : h ≤ h^(1-s) := by
  calc
    h = h^(1 : ℝ) := (Real.rpow_one h).symm
    _ ≤ h^(1-s) := Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)

/-- The small exponent increase at `α=0` and `α=s-1` is absorbed by
the prescribed loss. This works for every `K≥1`, including `K=1`. -/
theorem regMicro_endpoint_rate {K s α δ ε : ℝ}
    (hK : 1 ≤ K) (hδ : 2*δ ≤ ε/2) (hε : 0 ≤ ε) :
    K^(ε/2)*(K^(2*(α+δ))+K^(3*s-2)) ≤
      K^ε*(K^(2*α)+K^(3*s-2)) := by
  have hK0 : 0 < K := by linarith
  simp only [mul_add, ← Real.rpow_add hK0]
  apply add_le_add
  · exact Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hK (by linarith)

/-- Once the microscopic length is bounded by a fixed positive number,
any uniform second-moment bound is absorbed into the required rate.
The constant is chosen before `K`. No sign restriction on `α` is needed. -/
theorem regMicro_bounded_length_rate (B A s α ε : ℝ)
    (hB : 1 ≤ B) (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → K ≤ B →
      A ≤ C*K^ε*(K^(2*α)+K^(3*s-2)) := by
  have hB0 : 0 < B := by linarith
  let q := min (2*α) 0
  have hp : 0 < B^q := Real.rpow_pos_of_pos hB0 q
  refine ⟨(max A 0+1)/B^q, by positivity, fun K hK hKB => ?_⟩
  have hK0 : 0 < K := by linarith
  have hbase : B^q ≤ K^(2*α) :=
    (Real.rpow_le_rpow_of_nonpos hK0 hKB (min_le_right _ _)).trans
      (Real.rpow_le_rpow_of_exponent_le hK (min_le_left _ _))
  have hsum : B^q ≤ K^(2*α)+K^(3*s-2) :=
    hbase.trans (le_add_of_nonneg_right (Real.rpow_nonneg hK0.le _))
  have hpow : 1 ≤ K^ε := Real.one_le_rpow hK hε
  have hC : 0 ≤ (max A 0+1)/B^q := by positivity
  calc
    A ≤ max A 0+1 := by linarith [le_max_left A 0]
    _ = ((max A 0+1)/B^q)*B^q := by field_simp
    _ ≤ ((max A 0+1)/B^q)*K^ε*B^q := by
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hpow) hp.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end Riesz1.Internal
