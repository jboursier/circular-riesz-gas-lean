/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonComparator
public import Riesz1.Variance.APrioriCutoffComplete
public import Riesz1.Variance.APrioriRotationTranslationBound

/-!
# Localized statistics in the a priori bound

The differential, polynomial supremum bound, and negligible removed
statistic in the proof of Lemma 5.2. The localized sum
is written using the window and anchored coordinates. No second
definition of the statistic or cutoff is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set

namespace Riesz1.Internal

/-- The exact differential of `F*γ`, for any fixed set of labels.
The derivative of the pinned coordinate is included as the zero
functional `anchorCoord n 0`. -/
theorem localizedStatistic_hasFDerivAt (n : ℕ) (ℓ : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (I : Finset (Fin (n.succPNat : ℕ))) (y : Fin n → ℝ) :
    HasFDerivAt (fun z : Fin n → ℝ => ∑ i ∈ I, f (anchorVector z i / ℓ))
      (∑ i ∈ I, (deriv f (anchorVector y i / ℓ) / ℓ) • anchorCoord n i) y := by
  have hi (i : Fin (n.succPNat : ℕ)) : HasFDerivAt
      (fun z : Fin n → ℝ => f (anchorVector z i / ℓ))
      ((deriv f (anchorVector y i / ℓ) / ℓ) • anchorCoord n i) y := by
    have hcoord := ((anchorCoord n i).hasFDerivAt (x := y)).const_mul ℓ⁻¹
    have h := (((hf.differentiable one_ne_zero) _).hasDerivAt).comp_hasFDerivAt y hcoord
    simpa only [Function.comp_def, anchorCoord_apply, div_eq_inv_mul, smul_smul, mul_comm] using h
  convert HasFDerivAt.sum (fun i _ => hi i) using 1
  ext z
  simp only [Finset.sum_apply]

/-- The normalized localized statistic is uniformly polynomially
bounded on the whole ambient anchored carrier, not only on the good
event. Part of the proof of Lemma 5.2. -/
theorem localizedStatistic_abs_le (n : ℕ) {ℓ γ s lam ε : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ ((n : ℝ) + 1) * ℓ) (hγ : 0 ≤ γ)
    (hs : s < 2) (hlam : 0 ≤ lam) (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f (1 / ℓ))
    (hzero : f (1 / ℓ / 2) = 0)
    (hder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ cutoffMajorant s lam (((n : ℝ) + 1) * ℓ) |u|)
    (y : Fin n → ℝ) :
    |∑ i ∈ window n.succPNat (((n : ℝ) + 1) * ℓ) γ, f (anchorVector y i / ℓ)| ≤
      (9 * kernelSupConst s lam ε) * (((n : ℝ) + 1) * ℓ) ^ (γ + lam + ε) := by
  let K := ((n : ℝ) + 1) * ℓ
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hB : 0 ≤ kernelSupConst s lam ε * K ^ (lam + ε) := by
    dsimp [kernelSupConst]
    have : 0 < lam + ε := by linarith
    have : 0 < 2 - s := by linarith
    positivity
  have hsup (u : ℝ) : |f u| ≤ kernelSupConst s lam ε * K ^ (lam + ε) :=
    abs_le_kernelSup hs hK hlam hε (by positivity) hf hper hzero hder u
  have hcard : ((window n.succPNat K γ).card : ℝ) ≤ 9 * K ^ γ :=
    card_window_le_of_one_le hK hγ
  calc _ ≤ ∑ i ∈ window n.succPNat K γ, |f (anchorVector y i / ℓ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ window n.succPNat K γ, kernelSupConst s lam ε * K ^ (lam + ε) :=
        Finset.sum_le_sum fun i _ => hsup _
    _ = ((window n.succPNat K γ).card : ℝ) * (kernelSupConst s lam ε * K ^ (lam + ε)) := by
        simp only [sum_const, nsmul_eq_mul]
    _ ≤ (9 * K ^ γ) * (kernelSupConst s lam ε * K ^ (lam + ε)) :=
        mul_le_mul_of_nonneg_right hcard hB
    _ = _ := by
        change (9 * K ^ γ) * (kernelSupConst s lam ε * K ^ (lam + ε)) =
          (9 * kernelSupConst s lam ε) * K ^ (γ + lam + ε)
        rw [show γ + lam + ε = γ + (lam + ε) by ring, Real.rpow_add hK0 γ (lam + ε)]
        ring

/-- Removing the good-event cutoff costs an arbitrarily small inverse
power in `L²` for the normalized localized statistic. The constant is
chosen before `n`, `ℓ`, and `f`. Part of the proof of Lemma 5.2.
-/
theorem localizedStatistic_removed_L2 (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (γ lam ε b : ℝ)
    (hγ : 1 < γ) (hlam : 0 ≤ lam) (hε : 0 < ε) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ,
      0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n : ℝ) + 1) * ℓ →
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
        f (1 / ℓ / 2) = 0 →
        (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
          |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
        eLpNorm (fun y : Fin n → ℝ =>
          (1 - anchoredCutoff n.succPNat P.val.2 (((n : ℝ) + 1) * ℓ) γ ε y) *
            ∑ i ∈ window n.succPNat (((n : ℝ) + 1) * ℓ) γ, f (anchorVector y i / ℓ)) 2
          ((gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)) ≤
            ENNReal.ofReal (C * (((n : ℝ) + 1) * ℓ) ^ (-b)) := by
  have hM : 0 < 9 * kernelSupConst P.val.2 lam ε := by
    dsimp [kernelSupConst]
    have : 0 < lam + ε := by linarith
    have : 0 < 2 - P.val.2 := by linarith [P.2.2.2]
    positivity
  obtain ⟨C, hC, hc⟩ := a_priori_cutoff_complete hBE hPL P γ ε hγ hε
    (γ + lam + ε) (9 * kernelSupConst P.val.2 lam ε) b (by linarith) hM hb
  refine ⟨C, hC, fun n hn ℓ hℓ hℓ1 hK f hf hper hzero hder => ?_⟩
  apply (hc n hn forcingCutoff isForcingCutoff_forcingCutoff ℓ hℓ hℓ1 hK).2
  · apply Finset.measurable_sum
    intro i _
    apply hf.continuous.measurable.comp
    simpa only [anchorCoord_apply] using (anchorCoord n i).continuous.measurable.div_const ℓ
  · intro y
    exact localizedStatistic_abs_le n hℓ hK (by linarith) (by linarith [P.2.2.2])
      hlam hε hf hper hzero hder y

end Riesz1.Internal

end
