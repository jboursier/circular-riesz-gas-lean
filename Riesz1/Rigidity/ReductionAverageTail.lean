/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CenteredLogMgfTail
public import Riesz1.Rigidity.ForcingComparison
public import Riesz1.ToMathlib.TotalVariation.VarianceTransfer

/-!
# Tail of one centered increment, transferred from the constrained law

Part of the proof of Lemma 4.4. For a probability measure `μ` (the Gibbs law) and a probability
measure `ν` (a constrained law `Q_m`), a measurable real function `G` whose centered exponential moments
under `ν` satisfy `log E_ν exp(t (G - E_ν G)) ≤ K t²` has, for every threshold `w ≥ 1` with `|E_ν G| ≤ 1/2`,
the tail bound `μ(w ≤ |G|) ≤ TV(μ, ν) + 2 exp(-w²/(16 K))`. The two summands are the total-variation
transfer and the Chernoff tail under `ν`.

The exponent algebra `reduction_av_exponent_le` turns `w²/(16K)` into a multiple of `k^{ε/(s+2)}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- **Tail transfer.** Let `μ, ν` be probability measures and `G` a measurable real function. Let
`K > 0`, `w ≥ 1`, and suppose `|E_ν G| ≤ 1/2` and `log E_ν exp(t (G - E_ν G)) ≤ K t²` for every real `t`.
Then `μ(w ≤ |G|) ≤ TV(μ, ν) + 2 exp(-w²/(16K))`. -/
theorem measureReal_le_totalVariation_add_of_centered
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {G : Ω → ℝ} (hG : Measurable G) {K w : ℝ} (hK : 0 < K) (hw : 1 ≤ w)
    (hmean : |∫ ω, G ω ∂ν| ≤ 1 / 2)
    (hI : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * (G ω - ∫ ω', G ω' ∂ν))) ν)
    (hlog : ∀ t : ℝ, Real.log (∫ ω, Real.exp (t * (G ω - ∫ ω', G ω' ∂ν)) ∂ν) ≤ K * t ^ 2) :
    μ.real {ω | w ≤ |G ω|} ≤ totalVariation μ ν + 2 * Real.exp (-w ^ 2 / (16 * K)) := by
  have hA : MeasurableSet {ω | w ≤ |G ω|} := measurableSet_le measurable_const (continuous_abs.measurable.comp hG)
  have h1 := abs_measureReal_sub_le_totalVariation μ ν hA
  have h2 : ν.real {ω | w ≤ |G ω|} ≤ ν.real {ω | w / 2 ≤ |G ω - ∫ ω', G ω' ∂ν|} := by
    refine measureReal_mono fun ω hω => ?_
    have hω' : w ≤ |G ω| := hω
    have hm := abs_sub_abs_le_abs_sub (G ω) (∫ ω', G ω' ∂ν)
    show w / 2 ≤ |G ω - ∫ ω', G ω' ∂ν|
    linarith
  have h3 := measureReal_abs_le_of_log_mgf ν (v := w / 2)
    (Y := fun ω => G ω - ∫ ω', G ω' ∂ν) hK hI hlog (by linarith)
  have he : -(w / 2) ^ 2 / (4 * K) = -w ^ 2 / (16 * K) := by ring
  rw [he] at h3
  have h4 := (abs_le.mp h1).2
  linarith

/-- **Exponent algebra.** Let `s, ε > 0`, let `q` be a real number with `2/ε ≤ q` and `2 ≤ q`, let
`C_s > 0` and `k ≥ 1`. Then the exponent `(k^{s/2+ε}/q)² / (16 C_s k^{s+1/q+ε})` of the Chernoff bound
is at least `k^{ε/(s+2)}/(16 q² C_s)`. -/
theorem reduction_av_exponent_le {s ε q Cs k : ℝ} (hs : 0 < s) (hε : 0 < ε) (hq : 2 ≤ q)
    (hqε : 2 / ε ≤ q) (hCs : 0 < Cs) (hk : 1 ≤ k) :
    -(k ^ (s / 2 + ε) / q) ^ 2 / (16 * (Cs * k ^ (s + 1 / q + ε))) ≤
      -(1 / (16 * q ^ 2 * Cs)) * k ^ (ε / (s + 2)) := by
  have hk0 : 0 < k := by linarith
  have hq0 : 0 < q := by linarith
  have hsq : (k ^ (s / 2 + ε)) ^ 2 = k ^ (s + 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
    congr 1
    push_cast
    ring
  have hsplit : k ^ (s + 2 * ε) = k ^ (s + 1 / q + ε) * k ^ (ε - 1 / q) := by
    rw [← Real.rpow_add hk0]
    congr 1
    ring
  have hq' : 1 / q ≤ ε / 2 := by
    rw [div_le_iff₀ hq0]
    rw [div_le_iff₀ hε] at hqε
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hcomp : ε / (s + 2) ≤ ε - 1 / q := by
    have h2 : ε / (s + 2) ≤ ε / 2 := div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
    linarith
  have hpow : k ^ (ε / (s + 2)) ≤ k ^ (ε - 1 / q) := Real.rpow_le_rpow_of_exponent_le hk hcomp
  have hkp : k ^ (s + 1 / q + ε) ≠ 0 := (Real.rpow_pos_of_pos hk0 _).ne'
  have hL : -(k ^ (s / 2 + ε) / q) ^ 2 / (16 * (Cs * k ^ (s + 1 / q + ε))) =
      -(k ^ (ε - 1 / q)) / (16 * q ^ 2 * Cs) := by
    rw [div_pow, hsq, hsplit]
    field_simp
  have hR : -(1 / (16 * q ^ 2 * Cs)) * k ^ (ε / (s + 2)) =
      -(k ^ (ε / (s + 2))) / (16 * q ^ 2 * Cs) := by
    ring
  rw [hL, hR]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end Riesz1

end
