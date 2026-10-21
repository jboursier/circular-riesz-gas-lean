/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationTranslationGood
public import Riesz1.Variance.APrioriGoodComplete
public import Riesz1.Rigidity.RigidityTheorem
public import Riesz1.Frozen.External.BakryEmery
public import Riesz1.Frozen.External.PrekopaLeindler
public import Riesz1.ToMathlib.Calculus.PeriodicDerivativeTail
public import Riesz1.ToMathlib.Calculus.CutoffMajorant

/-!
# Uniform and probabilistic bounds for the translation error

Translation error in the proof of Lemma 5.2. These bounds control the bad part of
the `L²` estimate:

* the kernel is bounded: `|f u| ≤ C_s,λ,ε K^{λ+ε}` for every real `u`, by the periodic tail bound
  of `Riesz1.abs_le_intervalIntegral_of_periodic`, with the derivative majorant of
  `Riesz1.cutoffMajorant`.
* the translation error is bounded uniformly in the shift and the anchored vector, by
  `2 · |I_γ| · sup|f| ≤ 18 K^γ sup|f|`.
* the good-event cutoff has probability `C K^{-B}` of failing, from
  `Riesz1.Internal.aPrioriGood_complete_of_rigidity`, with the rigidity conclusion obtained from
  the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
  `External.PrekopaLeindler`, which are explicit hypotheses.
-/

@[expose] public section

open MeasureTheory Set

namespace Riesz1

/-- The derivative majorant of `cutoffMajorant` is nonnegative for a positive window scale. -/
theorem cutoffMajorant_nonneg' {s lam K : ℝ} (hK : 0 < K) (t : ℝ) :
    0 ≤ cutoffMajorant s lam K t := by
  unfold cutoffMajorant majorantNear majorantFar
  apply add_nonneg
  · split_ifs
    · exact div_nonneg zero_le_one (Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.2 hK.le)) _)
    · exact le_rfl
  · split_ifs with h
    · exact div_nonneg zero_le_one (Real.rpow_nonneg (by linarith) _)
    · exact le_rfl

/-- The constant of the kernel supremum bound, the constant of `integral_cutoffMajorant_le`. -/
noncomputable def kernelSupConst (s lam ε : ℝ) : ℝ :=
  2 ^ (ε + (1 + lam + ε)) / (lam + ε) + 2 ^ (3 - s) / (2 - s)

/-- **Kernel supremum.** Let `f` be `C¹` with period `L > 0` and `f (L/2) = 0`, and let the
derivative satisfy the majorant `cutoffMajorant s λ K` on the half period. Then `|f u|` is at most
`kernelSupConst s λ ε K^{λ+ε}` for every real `u`. -/
theorem abs_le_kernelSup {s lam K ε L : ℝ} (hs : s < 2) (hK : 1 ≤ K) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hL : 0 < L) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f L) (hzero : f (L / 2) = 0)
    (hder : ∀ u ∈ Icc (-(L / 2)) (L / 2), |deriv f u| ≤ cutoffMajorant s lam K |u|) (u : ℝ) :
    |f u| ≤ kernelSupConst s lam ε * K ^ (lam + ε) := by
  -- Every real `u` has a representative in the half period with the same value.
  obtain ⟨v, hv, hfv⟩ := hper.exists_mem_Ico hL u (-(L / 2))
  have hvI : v ∈ Icc (-(L / 2)) (L / 2) := ⟨hv.1, by linarith [hv.2]⟩
  have hbound : |f v| ≤ ∫ t in (0 : ℝ)..(L / 2), cutoffMajorant s lam K t := by
    have hB : ∀ᵐ t ∂volume, t ∈ Icc (-(L / 2)) (L / 2) → |deriv f t| ≤ cutoffMajorant s lam K |t| :=
      ae_of_all _ fun t ht => hder t ht
    have h1 := abs_le_intervalIntegral_of_periodic hL hf hper hzero
      (cutoffMajorant_intervalIntegrable hs hK hlam 0 (L / 2)) hB hvI
    refine h1.trans ?_
    have habs : |v| ≤ L / 2 := abs_le.2 ⟨by linarith [hvI.1], hvI.2⟩
    have hnn : ∀ t : ℝ, 0 ≤ cutoffMajorant s lam K t := fun t =>
      cutoffMajorant_nonneg' (by linarith) t
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (cutoffMajorant_intervalIntegrable hs hK hlam 0 |v|)
      (cutoffMajorant_intervalIntegrable hs hK hlam |v| (L / 2))
    have hpos : 0 ≤ ∫ t in (0 : ℝ)..|v|, cutoffMajorant s lam K t :=
      intervalIntegral.integral_nonneg (abs_nonneg v) fun t _ => hnn t
    linarith [hsplit, hpos]
  have hK' := integral_cutoffMajorant_le (s := s) (lam := lam) (K := K) (ε := ε) hs hK hlam hε
    (by linarith : 0 ≤ L / 2)
  rw [hfv]
  exact hbound.trans hK'

/-- **Uniform bound of the translation error.** For every shift `D` and every anchored vector `y`,
the translation error is at most `2 · 9 K^γ` times the kernel supremum, where `K = N ℓ`. -/
theorem abs_translationError_le_uniform (N : ℕ+) {ℓ γ s lam ε : ℝ} (hs : s < 2) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ)
    (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) (hε : 0 < ε) (hℓ : 0 < ℓ) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f (1 / ℓ)) (hzero : f (1 / ℓ / 2) = 0)
    (hder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ cutoffMajorant s lam (((N : ℕ) : ℝ) * ℓ) |u|) (D : ℝ)
    (y : Fin (N : ℕ) → ℝ) :
    |translationError N ℓ γ f D y| ≤
      2 * (9 * (((N : ℕ) : ℝ) * ℓ) ^ γ) * (kernelSupConst s lam ε * (((N : ℕ) : ℝ) * ℓ) ^ (lam + ε)) := by
  set K : ℝ := ((N : ℕ) : ℝ) * ℓ with hK_def
  have hS : ∀ u : ℝ, |f u| ≤ kernelSupConst s lam ε * K ^ (lam + ε) := fun u =>
    abs_le_kernelSup hs hK hlam hε (by positivity) hf hper hzero hder u
  have hsum : ∀ (I : Finset (Fin (N : ℕ))) (g : Fin (N : ℕ) → ℝ),
      |∑ i ∈ I, f (g i)| ≤ (I.card : ℝ) * (kernelSupConst s lam ε * K ^ (lam + ε)) := by
    intro I g
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul I (fun i => |f (g i)|)
      (kernelSupConst s lam ε * K ^ (lam + ε)) (fun i _ => hS (g i))
    rw [nsmul_eq_mul] at this
    exact this
  unfold translationError
  have hcard := card_window_le_of_one_le (N := N) (K := K) (γ := γ) hK hγ
  have hS0 : 0 ≤ kernelSupConst s lam ε * K ^ (lam + ε) :=
    mul_nonneg (by
      unfold kernelSupConst
      have h1 : 0 ≤ 2 ^ (ε + (1 + lam + ε)) / (lam + ε) :=
        div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
      have h2 : 0 ≤ 2 ^ (3 - s) / (2 - s) :=
        div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
      linarith) (Real.rpow_nonneg (by linarith) _)
  have hA' : |∑ i ∈ window N K γ, f ((((N : ℕ) : ℝ) * y i - D) / K)| ≤
      9 * K ^ γ * (kernelSupConst s lam ε * K ^ (lam + ε)) := by
    refine (hsum (window N K γ) (fun i => (((N : ℕ) : ℝ) * y i - D) / K)).trans ?_
    exact mul_le_mul_of_nonneg_right hcard hS0
  have hB' : |∑ i ∈ window N K γ, f (y i / ℓ)| ≤
      9 * K ^ γ * (kernelSupConst s lam ε * K ^ (lam + ε)) := by
    refine (hsum (window N K γ) (fun i => y i / ℓ)).trans ?_
    exact mul_le_mul_of_nonneg_right hcard hS0
  calc |∑ i ∈ window N K γ, f ((((N : ℕ) : ℝ) * y i - D) / K) -
          ∑ i ∈ window N K γ, f (y i / ℓ)|
      ≤ |∑ i ∈ window N K γ, f ((((N : ℕ) : ℝ) * y i - D) / K)| +
          |∑ i ∈ window N K γ, f (y i / ℓ)| := abs_sub _ _
    _ ≤ 2 * (9 * K ^ γ) * (kernelSupConst s lam ε * K ^ (lam + ε)) := by linarith [hA', hB']

/-- **Probability of the bad event.** For `β > 0`, `s ∈ (0,1)`, `γ > 1` and `ε > 0`, and every
`B > 0`, the good-event cutoff fails with probability `C K^{-B}`, uniformly in `N` and `ℓ` with
`K = N ℓ ≥ 1`. The rigidity conclusion comes from the hypotheses `External.BakryEmery` and
`External.PrekopaLeindler`. -/
theorem gibbs_bad_bound (P : Parameters) (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) {γ : ℝ} (hγ : 1 < γ) {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ), 2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 →
      1 ≤ ((N : ℕ) : ℝ) * ℓ →
      gibbsMeasure P N {X | goodCutoff N P.val.2 (((N : ℕ) : ℝ) * ℓ) γ ε X ≠ 1} ≤
        ENNReal.ofReal (C * (((N : ℕ) : ℝ) * ℓ) ^ (-B)) := by
  obtain ⟨⟨beta, s⟩, hbeta, hs, hs1⟩ := P
  obtain ⟨C, hC, hbd⟩ :=
    (Internal.aPrioriGood_complete_of_rigidity beta s hbeta hs hs1
      (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1) γ hγ).1 ε hε B hB
  refine ⟨C, hC, fun N ℓ hN hℓ hℓ1 hK1 => ?_⟩
  have hKN : ((N : ℕ) : ℝ) * ℓ ≤ ((N : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  exact hbd hPL N hN _ hK1 hKN

end Riesz1
