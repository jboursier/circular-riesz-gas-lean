/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.CircleSobolevSq
public import Riesz1.Frozen.RieszConstant
public import Riesz1.Frozen.RieszRepresentative
public import Riesz1.Kernel.Coefficients
public import Riesz1.Kernel.Fourier
public import Riesz1.ToMathlib.HurwitzKernel.Mean
public import Riesz1.ToMathlib.HurwitzKernel.Regularity
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Power-law energy of the periodic Riesz kernel

Part of Lemma 2.3. For `0 < α < s / 2` the representative `g_α`
lies in `L²(𝕋)`, has mean zero, and has the explicit `H^{(1-s)/2}` seminorm
`ζ(1 + s - 2α, 1)`. The Fourier coefficients come from `fourierCoeff_rieszRepresentative`.
This file proves square integrability from the Euler decomposition and then sums the
Fourier series.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real Interval

namespace Riesz1

/-- The Euler remainder of the Riesz representative is bounded on `(0,1)`: after the two
power singularities are removed, a bounded function remains. -/
private lemma exists_bound_rieszRepresentative_remainder (α : RieszExponent) :
    ∃ M : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
      |(∑' n, eulerTermC α.val (t : ℂ) n).re + (∑' n, eulerTermC α.val ((1 - t : ℝ) : ℂ) n).re -
        2 / (1 - α.val)| ≤ M := by
  have hα0 : 0 < α.val := α.property.1
  have hα1 : α.val < 1 := α.property.2
  have hQc : ContinuousOn (fun t : ℝ => (∑' n, eulerTermC α.val (t : ℂ) n).re) (Icc 0 1) :=
    fun t ht => (contDiffAt_euler_remainder α.val hα0 hα1 t (by linarith [ht.1])).continuousAt
      |>.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hQc
  refine ⟨2 * B + 2 / (1 - α.val), fun t ht => ?_⟩
  have h1 := hB t ⟨ht.1.le, ht.2.le⟩
  have h2 := hB (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [Real.norm_eq_abs] at h1 h2
  have hc : 0 ≤ 2 / (1 - α.val) := div_nonneg (by norm_num) (by linarith)
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- On `(0,1)` the Riesz representative is the two power singularities plus the bounded
Euler remainder of `exists_bound_rieszRepresentative_remainder`. -/
private lemma rieszRepresentative_eq_powers (α : RieszExponent) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    rieszRepresentative α (t : UnitAddCircle) = t ^ (-α.val) + (1 - t) ^ (-α.val) +
      ((∑' n, eulerTermC α.val (t : ℂ) n).re + (∑' n, eulerTermC α.val ((1 - t : ℝ) : ℂ) n).re -
        2 / (1 - α.val)) := by
  have h := hurwitzZetaEven_re_euler α.val α.property.1 α.property.2 t ht.1 ht.2
  unfold rieszRepresentative
  rw [h]
  ring

/-- Algebra behind the square bound: `(x + y + R)² ≤ 3 (x² + y² + M²)` when `|R| ≤ M`. -/
private lemma sq_sum_three_le (x y R M : ℝ) (hR : |R| ≤ M) :
    (x + y + R) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + M ^ 2) := by
  have hR0 : 0 ≤ |R| := abs_nonneg R
  have hR2 : R ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs R]
    nlinarith [mul_nonneg (sub_nonneg.2 hR) (add_nonneg hR0 (le_trans hR0 hR))]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - R), sq_nonneg (x - R)]

/-- The square of the Riesz representative is interval integrable on `(0,1)` when the exponent
is below one half. -/
private lemma intervalIntegrable_sq_rieszRepresentative (α : RieszExponent)
    (hα : α.val < 1 / 2) :
    IntervalIntegrable (fun t : ℝ => rieszRepresentative α (t : UnitAddCircle) ^ 2) volume 0 1 := by
  obtain ⟨M, hM⟩ := exists_bound_rieszRepresentative_remainder α
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, rieszRepresentative α (t : UnitAddCircle) ^ 2 ≤
      3 * (t ^ (-(2 * α.val)) + (1 - t) ^ (-(2 * α.val)) + M ^ 2) := by
    intro t ht
    have hx : (t ^ (-α.val)) ^ 2 = t ^ (-(2 * α.val)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
      congr 1
      push_cast
      ring
    have hy : ((1 - t) ^ (-α.val)) ^ 2 = (1 - t) ^ (-(2 * α.val)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [ht.2])]
      congr 1
      push_cast
      ring
    rw [rieszRepresentative_eq_powers α ht, ← hx, ← hy]
    exact sq_sum_three_le _ _ _ M (hM t ht)
  have hG : IntervalIntegrable
      (fun t : ℝ => 3 * (t ^ (-(2 * α.val)) + (1 - t) ^ (-(2 * α.val)) + M ^ 2)) volume 0 1 := by
    have h1 : IntervalIntegrable (fun t : ℝ => t ^ (-(2 * α.val))) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h2 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(2 * α.val))) volume 0 1 := by
      simpa using (h1.comp_sub_left 1).symm
    exact ((h1.add h2).add intervalIntegrable_const).const_mul 3
  have hmeas : AEStronglyMeasurable (fun t : ℝ => rieszRepresentative α (t : UnitAddCircle) ^ 2)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    have hg : AEStronglyMeasurable (fun t : ℝ => rieszRepresentative α (t : UnitAddCircle))
        (volume.restrict (Ioc 0 (0 + 1))) :=
      (integrable_rieszRepresentative α).aestronglyMeasurable.comp_measurePreserving
        (AddCircle.measurePreserving_mk (T := 1) 0)
    rw [zero_add] at hg
    rw [uIoc_of_le zero_le_one]
    exact hg.pow 2
  refine IntervalIntegrable.mono_fun' hG hmeas ?_
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
    rw [ae_iff]
    simp
  show ∀ᵐ t : ℝ ∂(volume.restrict (Ι (0 : ℝ) 1)),
    ‖rieszRepresentative α (t : UnitAddCircle) ^ 2‖ ≤
      3 * (t ^ (-(2 * α.val)) + (1 - t) ^ (-(2 * α.val)) + M ^ 2)
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hae] with t ht hmem
  rw [uIoc_of_le zero_le_one] at hmem
  have hmem' : t ∈ Ioo (0 : ℝ) 1 := ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hpt t hmem'

/-- The Riesz representative `g_α` is square integrable on the unit circle for `α < 1 / 2`. -/
private lemma memLp_two_rieszRepresentative (α : RieszExponent) (hα : α.val < 1 / 2) :
    MemLp (fun x : UnitAddCircle => (rieszRepresentative α x : ℂ)) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    (integrable_rieszRepresentative_complex α).aestronglyMeasurable).mpr ?_
  have hI : Integrable (fun x : UnitAddCircle => rieszRepresentative α x ^ 2) :=
    integrable_unitAddCircle_of_interval (intervalIntegrable_sq_rieszRepresentative α hα)
  refine hI.congr (ae_of_all _ fun x => ?_)
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Squared Fourier modulus of `g_α` at a nonzero mode, as a real square. -/
private lemma norm_sq_fourierCoeff_rieszRepresentative (α : RieszExponent) (k : ℤ) :
    ‖fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative α x : ℂ)) k‖ ^ 2 =
      if k = 0 then 0 else (rieszConstant α * (2 * Real.pi * |(k : ℝ)|) ^ (α.val - 1)) ^ 2 := by
  rw [fourierCoeff_rieszRepresentative]
  split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The zeta sum over the integers: `∑_{k ∈ ℤ} |k|^{-p} = 2 ζ(p)` for `p > 1`. -/
private lemma tsum_int_abs_rpow_eq (p : ℝ) (hp : 1 < p) :
    ∑' k : ℤ, |(k : ℝ)| ^ (-p) = 2 * (riemannZeta (p : ℂ)).re := by
  have hs : Summable (fun k : ℤ => |(k : ℝ)| ^ (-p)) := Real.summable_abs_int_rpow hp
  have hs1 : Summable (fun n : ℕ => |((n : ℤ) : ℝ)| ^ (-p)) :=
    hs.comp_injective Nat.cast_injective
  have hs2 : Summable (fun n : ℕ => |((-(n + 1) : ℤ) : ℝ)| ^ (-p)) :=
    hs.comp_injective (fun a b h => by simpa using h)
  have h0 : |(((0 : ℕ) : ℤ) : ℝ)| ^ (-p) = 0 := by
    simp only [Nat.cast_zero, Int.cast_zero, abs_zero]
    exact Real.zero_rpow (neg_ne_zero.mpr (by linarith))
  have hpos : ∀ n : ℕ, |(((n + 1 : ℕ) : ℤ) : ℝ)| ^ (-p) = ((n : ℝ) + 1) ^ (-p) := by
    intro n
    congr 1
    rw [Int.cast_natCast, Nat.cast_add_one]
    exact abs_of_nonneg (by positivity)
  have hneg : ∀ n : ℕ, |((-(n + 1) : ℤ) : ℝ)| ^ (-p) = ((n : ℝ) + 1) ^ (-p) := by
    intro n
    congr 1
    rw [Int.cast_neg, abs_neg]
    push_cast
    exact abs_of_nonneg (by positivity)
  have hA : ∑' n : ℕ, |((n : ℤ) : ℝ)| ^ (-p) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) := by
    rw [hs1.tsum_eq_zero_add, h0, zero_add]
    exact tsum_congr hpos
  have hB : ∑' n : ℕ, |((-(n + 1) : ℤ) : ℝ)| ^ (-p) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) :=
    tsum_congr hneg
  have hz : ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) : ℝ) : ℂ) = riemannZeta (p : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hp), Complex.ofReal_tsum]
    congr 1
    ext n
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rw [one_div, Complex.cpow_neg]
  have hC : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) = (riemannZeta (p : ℂ)).re := by
    rw [← hz, Complex.ofReal_re]
  have hsplit : ∑' k : ℤ, |(k : ℝ)| ^ (-p) =
      (∑' n : ℕ, |((n : ℤ) : ℝ)| ^ (-p)) + ∑' n : ℕ, |((-(n + 1) : ℤ) : ℝ)| ^ (-p) :=
    tsum_of_nat_of_neg_add_one (f := fun k : ℤ => |(k : ℝ)| ^ (-p)) hs1 hs2
  rw [hsplit, hA, hB, hC]
  ring

/-- Termwise identity: the `H^{(1-s)/2}` summand of `g_α` at a mode `k` is the constant
`c_α² (2π)^{2α-2}` times `|k|^{-(1 + s - 2α)}`, and both sides vanish at `k = 0`. -/
private lemma summand_eq (s α : RieszExponent) (hα : α.val < s.val / 2) (k : ℤ) :
    (if k = 0 then (0 : ENNReal) else ENNReal.ofReal (|(k : ℝ)| ^ (2 * ((1 - s.val) / 2)) *
        ‖fourierCoeff (fun x : UnitAddCircle => (rieszRepresentative α x : ℂ)) k‖ ^ 2)) =
      ENNReal.ofReal (rieszConstant α ^ 2 * (2 * Real.pi) ^ (2 * α.val - 2) *
        |(k : ℝ)| ^ (-(1 + s.val - 2 * α.val))) := by
  by_cases hk : k = 0
  · subst hk
    have hp0 : -(1 + s.val - 2 * α.val) ≠ 0 := by
      intro h
      linarith [s.property.2, α.property.1]
    simp only [↓reduceIte, Int.cast_zero, abs_zero, Real.zero_rpow hp0, mul_zero,
      ENNReal.ofReal_zero]
  · simp only [hk, ↓reduceIte, norm_sq_fourierCoeff_rieszRepresentative]
    congr 1
    have hx : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
    have e1 : (2 * Real.pi * |(k : ℝ)|) ^ (α.val - 1) =
        (2 * Real.pi) ^ (α.val - 1) * |(k : ℝ)| ^ (α.val - 1) :=
      Real.mul_rpow (by positivity) hx.le
    have e2 : ((2 * Real.pi) ^ (α.val - 1)) ^ 2 = (2 * Real.pi) ^ (2 * α.val - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    have e3 : (|(k : ℝ)| ^ (α.val - 1)) ^ 2 * |(k : ℝ)| ^ (2 * ((1 - s.val) / 2)) =
        |(k : ℝ)| ^ (-(1 + s.val - 2 * α.val)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
      congr 1
      push_cast
      ring
    calc |(k : ℝ)| ^ (2 * ((1 - s.val) / 2)) *
          (rieszConstant α * (2 * Real.pi * |(k : ℝ)|) ^ (α.val - 1)) ^ 2
        = rieszConstant α ^ 2 * (((2 * Real.pi) ^ (α.val - 1)) ^ 2 *
            ((|(k : ℝ)| ^ (α.val - 1)) ^ 2 * |(k : ℝ)| ^ (2 * ((1 - s.val) / 2)))) := by
          rw [e1]
          ring
      _ = rieszConstant α ^ 2 * (2 * Real.pi) ^ (2 * α.val - 2) *
            |(k : ℝ)| ^ (-(1 + s.val - 2 * α.val)) := by
          rw [e2, e3]
          ring

/-- Power-law energy (part of Lemma 2.3).

For `0 < α < s/2` the Riesz representative `g_α` lies in `L²(𝕋)` and has mean zero. For every
`L²` proof `hg`, its `H^{(1-s)/2}` seminorm is finite and satisfies
`(2π)^{1-s}/(2βc_s) ‖g_α‖² = (2π)^{-1+2α-s} c_α²/(βc_s) ζ(1+s-2α, 1)`. -/
theorem explicit_formulas_power (s α : RieszExponent) (hα : α.val < s.val / 2) (β : ℝ)
    (hβ : 0 < β) :
    MemLp (fun x : UnitAddCircle => (rieszRepresentative α x : ℂ)) 2 volume ∧
      (∫ x : UnitAddCircle, rieszRepresentative α x = 0) ∧
      ∀ hg : MemLp (fun x : UnitAddCircle => (rieszRepresentative α x : ℂ)) 2 volume,
        circleSobolevSq ((1 - s.val) / 2)
            ⟨fun x : UnitAddCircle => (rieszRepresentative α x : ℂ), hg⟩ ≠ ⊤ ∧
        (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
            (circleSobolevSq ((1 - s.val) / 2)
              ⟨fun x : UnitAddCircle => (rieszRepresentative α x : ℂ), hg⟩).toReal =
          (2 * Real.pi) ^ (-1 + 2 * α.val - s.val) * rieszConstant α ^ 2 /
            (β * rieszConstant s) * (riemannZeta ((1 + s.val - 2 * α.val : ℝ) : ℂ)).re := by
  have hα' : α.val < 1 / 2 := by linarith [s.property.2]
  have hp : 1 < 1 + s.val - 2 * α.val := by linarith
  have hcs : 0 < rieszConstant s := by
    unfold rieszConstant
    exact div_pos (mul_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr Real.pi_pos))
      (Real.Gamma_pos_of_pos (by linarith [s.property.1, s.property.2])))
      (Real.Gamma_pos_of_pos (by linarith [s.property.1]))
  refine ⟨memLp_two_rieszRepresentative α hα', integral_rieszRepresentative α, fun hg => ?_⟩
  have hnn : 0 ≤ ∑' k : ℤ, rieszConstant α ^ 2 * (2 * Real.pi) ^ (2 * α.val - 2) *
      |(k : ℝ)| ^ (-(1 + s.val - 2 * α.val)) :=
    tsum_nonneg fun k => by positivity
  have hsum : circleSobolevSq ((1 - s.val) / 2)
      ⟨fun x : UnitAddCircle => (rieszRepresentative α x : ℂ), hg⟩ =
        ENNReal.ofReal (∑' k : ℤ, rieszConstant α ^ 2 * (2 * Real.pi) ^ (2 * α.val - 2) *
          |(k : ℝ)| ^ (-(1 + s.val - 2 * α.val))) := by
    unfold circleSobolevSq
    rw [tsum_congr (summand_eq s α hα), ENNReal.ofReal_tsum_of_nonneg
      (fun k => by positivity) ((Real.summable_abs_int_rpow hp).mul_left _)]
  refine ⟨by rw [hsum]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hsum, ENNReal.toReal_ofReal hnn, tsum_mul_left, tsum_int_abs_rpow_eq _ hp]
  have hsplit : (2 * Real.pi) ^ (-1 + 2 * α.val - s.val) =
      (2 * Real.pi) ^ (1 - s.val) * (2 * Real.pi) ^ (2 * α.val - 2) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [hsplit]
  field_simp

end Riesz1
