/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.InverseBlocks
public import Riesz1.ToMathlib.Moments.RpowLpBound

/-!
# `L^p` bounds for negative powers of block lengths

Part of Lemma 5.2 (the rotation part), exterior tail. For a block length `S_{j,L}` of the Gibbs
law and an exponent `q > 0`, the `L^p` seminorm of `α S_{j,L}^{-q}` is controlled by the inverse
block moments of Lemma 4.5 (`inverse_blocks_uniform`). The constant does not
depend on the number of particles `N`, the starting index `j`, or the block length `L`.
-/

@[expose] public section

open MeasureTheory

namespace Riesz1

/-- The `p`-th power of a `q`-th power: `(C^{1/p})^p = C` for `C ≥ 0` and `p ≠ 0`. -/
theorem rpow_one_div_rpow_pow {C p : ℝ} (hC : 0 ≤ C) (hp : p ≠ 0) :
    (C ^ (1 / p)) ^ p = C := by
  rw [← Real.rpow_mul hC, one_div_mul_cancel hp, Real.rpow_one]

/-- **`L^p` bound for a negative power under a moment bound.** Let `G > 0` be measurable with
`∫⁻ G^{-qp} ≤ C L^{-qp}`. Then `eLpNorm (α G^{-q}) p ≤ α C^{1/p} L^{-q}` for `α ≥ 0`. -/
theorem eLpNorm_rpow_neg_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {G : Ω → ℝ} (hG : Measurable G) (hG0 : ∀ x, 0 < G x) {q p L C α : ℝ} (_hq : 0 < q)
    (hp : 0 < p) (hC : 0 ≤ C) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hmom : ∫⁻ x, ENNReal.ofReal (G x ^ (-(q * p))) ∂μ ≤ ENNReal.ofReal (C * L ^ (-(q * p)))) :
    eLpNorm (fun x => α * G x ^ (-q)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (α * C ^ (1 / p) * L ^ (-q)) := by
  have hMnn : 0 ≤ α * C ^ (1 / p) * L ^ (-q) :=
    mul_nonneg (mul_nonneg hα (Real.rpow_nonneg hC _)) (Real.rpow_nonneg hL _)
  have hMp : (α * C ^ (1 / p) * L ^ (-q)) ^ p = α ^ p * (C * L ^ (-(q * p))) := by
    rw [Real.mul_rpow (mul_nonneg hα (Real.rpow_nonneg hC _)) (Real.rpow_nonneg hL _),
      Real.mul_rpow hα (Real.rpow_nonneg hC _), rpow_one_div_rpow_pow hC hp.ne',
      ← Real.rpow_mul hL, neg_mul]
    ring
  have hmeas : Measurable (fun x => α * G x ^ (-q)) :=
    measurable_const.mul (hG.pow_const (-q))
  refine eLpNorm_le_of_lintegral_rpow_le μ hmeas
    (fun x => mul_nonneg hα (Real.rpow_nonneg (hG0 x).le _)) hp hMnn ?_
  rw [hMp]
  have hpt : ∀ x, ENNReal.ofReal ((α * G x ^ (-q)) ^ p) =
      ENNReal.ofReal (α ^ p) * ENNReal.ofReal (G x ^ (-(q * p))) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hα _), Real.mul_rpow hα
      (Real.rpow_nonneg (hG0 x).le _), ← Real.rpow_mul (hG0 x).le, neg_mul]
  have hfin : ∫⁻ x, ENNReal.ofReal ((α * G x ^ (-q)) ^ p) ∂μ =
      ENNReal.ofReal (α ^ p) * ∫⁻ x, ENNReal.ofReal (G x ^ (-(q * p))) ∂μ := by
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hfin]
  calc ENNReal.ofReal (α ^ p) * ∫⁻ x, ENNReal.ofReal (G x ^ (-(q * p))) ∂μ
      ≤ ENNReal.ofReal (α ^ p) * ENNReal.ofReal (C * L ^ (-(q * p))) := by gcongr
    _ = ENNReal.ofReal (α ^ p * (C * L ^ (-(q * p)))) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hα _)]

/-- **Uniform `L^p` bound for block lengths.** For every `q > 0` and `p > 0` there is a constant
`C ≥ 0` such that, for every `N ≥ 1`, every `j ∈ ℤ`, every block length `L ≥ 1` and every
`α ≥ 0`, the `L^p` seminorm of `α S_{j,L}^{-q}` under the Gibbs law of `N` particles is at most
`α C^{1/p} L^{-q}`. The constant comes from `inverse_blocks_uniform` at the exponent `qp`. -/
theorem exists_eLpNorm_blockLength_rpow_neg_le (P : Parameters)
    (hPL : External.PrekopaLeindler) {q p : ℝ} (hq : 0 < q) (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ+) (j : ℤ) (L : ℕ), 0 < L → ∀ α : ℝ, 0 ≤ α →
      eLpNorm (fun X : Configuration N => α * blockLength X j L ^ (-q)) (ENNReal.ofReal p)
        (gibbsMeasure P N) ≤ ENNReal.ofReal (α * C ^ (1 / p) * (L : ℝ) ^ (-q)) := by
  obtain ⟨C, hC, hall⟩ := inverse_blocks_uniform P (p := q * p) (mul_pos hq hp)
  refine ⟨C, hC.le, fun N j L hL α hα => ?_⟩
  obtain ⟨_, hle⟩ := hall hPL N j L hL
  exact eLpNorm_rpow_neg_le_of_lintegral (gibbsMeasure P N) (measurable_blockLength j L)
    (fun X => blockLength_pos X j hL) hq hp hC.le (Nat.cast_nonneg L) hα hle

end Riesz1

end
