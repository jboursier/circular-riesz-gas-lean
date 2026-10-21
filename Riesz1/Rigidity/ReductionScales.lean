/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ReductionScalesBlock
public import Riesz1.Rigidity.ReductionScalesMean

/-!
# Bounds for the multiscale increments

Part of Lemma 4.4. Let `P` be the Gibbs parameters, with inverse temperature
`β = P.val.1` and exponent `s = P.val.2`, let `ε > 0`, let `q` be an integer with
`q ≥ max(2, 2/ε)`, and let `θ` be a forcing cutoff. The Bakry–Émery criterion
`External.BakryEmery` and the Prékopa–Leindler inequality `External.PrekopaLeindler`
enter as explicit hypotheses.

For every `N ≥ 2`, every label `i ∈ ℤ`, every scale `1 ≤ k ≤ ⌊N/2⌋` and every `0 ≤ m < q`, the
multiscale increments `G_m`, with constrained laws `Q_m` (`scaleIncrement`, `scaleLaw`), satisfy:

1. the telescoping identity `∑_{m<q} G_m = N (x_i - x_i^{[k]})`.
2. on the lifted block, `G_m` is a linear block functional whose partial derivatives over the block
   sum to zero and whose squared gradient is at most `4 N² k^{-m/q}`.
3. `|E_{Q_m} G_m| ≤ 1/2`.
4. `TV(P, Q_m) ≤ 3 exp(-c_0 k^{ε/(s+2)})` with `c_0 = (log 2)/4`.
5. for every real `t`, `log E_{Q_m} exp(t (G_m - E_{Q_m} G_m)) ≤ C t² k^{s(m+1)/q + 1/q + ε}`, and
   this is at most `C t² k^{s + 1/q + ε}`, with `C = 2^{s+3}/(β a_s)` depending only on `s` and `β`.

The constant `C` is chosen before `N`, `i`, `k`, `m`, `t`.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

/-- **Bounds for the multiscale increments**, part of Lemma 4.4. -/
theorem reduction_av_scales (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : 2 ≤ q) (_hqε : 2 / ε ≤ (q : ℝ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (i : ℤ) {k m : ℕ} (_hk : 1 ≤ k)
      (_hkN : 2 * k ≤ (N : ℕ)) (_hm : m < q),
      (∀ X : Configuration N,
          ∑ m' ∈ range q, scaleIncrement i k q m' X =
            ((N : ℕ) : ℝ) * (cyclicLift X i - blockAverage X i k)) ∧
      (∀ hL : cyclicRepSpan N (scaleIndex k q (m + 1)) < (N : ℕ), ∃ F :
          HsEuclidean (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1)))) → ℝ,
        (∀ X : Configuration N,
            F (WithLp.toLp 2 (liftedBlock (cyclicRepStart N (scaleIndex k q (m + 1)) i) hL X).val) =
              scaleIncrement i k q m X) ∧
        (∀ x, ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
            fderiv ℝ F x (EuclideanSpace.single r 1) = 0) ∧
        (∀ x, ‖fderiv ℝ F x‖ ^ 2 ≤ 4 * ((N : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ (-((m : ℝ) / q)))) ∧
      |∫ X, scaleIncrement i k q m X ∂scaleLaw P N θ ε i k q m| ≤ 1 / 2 ∧
      totalVariation (gibbsMeasure P N) (scaleLaw P N θ ε i k q m) ≤
        3 * Real.exp (-(Real.log 2 / 4) * (k : ℝ) ^ (ε / (P.val.2 + 2))) ∧
      ∀ t : ℝ,
        Integrable (fun X => Real.exp (t * (scaleIncrement i k q m X -
            ∫ Y, scaleIncrement i k q m Y ∂scaleLaw P N θ ε i k q m)))
          (scaleLaw P N θ ε i k q m) ∧
        Real.log (∫ X, Real.exp (t * (scaleIncrement i k q m X -
            ∫ Y, scaleIncrement i k q m Y ∂scaleLaw P N θ ε i k q m))
            ∂scaleLaw P N θ ε i k q m) ≤
          C * t ^ 2 * (k : ℝ) ^ (P.val.2 * ((m : ℝ) + 1) / q + 1 / q + ε) ∧
        Real.log (∫ X, Real.exp (t * (scaleIncrement i k q m X -
            ∫ Y, scaleIncrement i k q m Y ∂scaleLaw P N θ ε i k q m))
            ∂scaleLaw P N θ ε i k q m) ≤
          C * t ^ 2 * (k : ℝ) ^ (P.val.2 + 1 / q + ε) := by
  have hβ : 0 < P.val.1 := P.property.1
  have ha : 0 < rigidityCurvatureConstant (parametersExponent P).val :=
    rigidityCurvatureConstant_pos (parametersExponent P)
  have hs : 0 < P.val.2 := P.property.2.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set C : ℝ := 2 ^ (P.val.2 + 3) / (P.val.1 * rigidityCurvatureConstant (parametersExponent P).val)
    with hCdef
  have hCpos : 0 < C := div_pos (Real.rpow_pos_of_pos two_pos _) (mul_pos hβ ha)
  refine ⟨C, hCpos, ?_⟩
  intro N hN i k m hk hkN hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨fun X => sum_scaleIncrement i k (by omega : 0 < q) X, ?_, ?_, ?_, ?_⟩
  · intro hL
    refine ⟨scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1))), fun X =>
      scaleFun_liftedBlock N i hk hkN hm hL X, fun x =>
      sum_fderiv_scaleFun_single N i hk hkN hm x, fun x =>
      sq_norm_fderiv_scaleFun_le N i hk hkN hm x⟩
  · by_cases hsym : 2 * scaleIndex k q (m + 1) < (N : ℕ)
    · rw [integral_scaleIncrement_symmetric P N hN hθ ε i hk hkN hm hsym, abs_zero]
      norm_num
    · exact abs_integral_scaleIncrement_full P N hN hθ hε.le i hk hkN hm hsym
  · exact scale_totalVariation_le hPL P N hN hθ hε.le i hk hkN hm
  · intro t
    obtain ⟨h1, h2⟩ := scale_centered_moment hBE hPL P N hN hθ hε.le i hk hkN hm t
    have hmq : ((m : ℝ) + 1) / q ≤ 1 := by
      rw [div_le_one hq0]
      exact_mod_cast (show m + 1 ≤ q by omega)
    have hexp : P.val.2 * ((m : ℝ) + 1) / q ≤ P.val.2 := by
      rw [mul_div_assoc]
      exact mul_le_of_le_one_right hs.le hmq
    have hpow : (k : ℝ) ^ (P.val.2 * ((m : ℝ) + 1) / q + 1 / q + ε) ≤
        (k : ℝ) ^ (P.val.2 + 1 / q + ε) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    have hCt : 0 ≤ C * t ^ 2 := mul_nonneg hCpos.le (sq_nonneg t)
    refine ⟨h1, h2, h2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left hpow hCt

end Riesz1

end
