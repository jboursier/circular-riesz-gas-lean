/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriUnanchoredTail
public import Riesz1.Variance.APrioriAssembly
public import Riesz1.Variance.APrioriRotationAnchoredLaw

/-!
# Localized variance at the preceding particle

The size-biased variance step in Lemma 5.2, with
actual Sobolev membership supplied by the assembly and the
weighted gap tail proved from the exponential moment.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset

namespace Riesz1.Internal

/-- Uniform bound for the localized sum on the full ambient carrier of
the rotation law. No support restriction on the vector is needed. -/
theorem origin_localized_abs_le {N : ℕ+} {ℓ γ s lam ε : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hs : s < 2) (hlam : 0 ≤ lam) (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f (1 / ℓ))
    (hzero : f (1 / ℓ / 2) = 0)
    (hder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ cutoffMajorant s lam ((N : ℝ) * ℓ) |u|)
    (y : Fin (N : ℕ) → ℝ) :
    |∑ i ∈ window N ((N : ℝ) * ℓ) γ, f (y i / ℓ)| ≤
      (9 * kernelSupConst s lam ε) * ((N : ℝ) * ℓ) ^ (γ + lam + ε) := by
  let K := (N : ℝ) * ℓ
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hC : 0 ≤ kernelSupConst s lam ε := by
    dsimp [kernelSupConst]
    have : 0 < lam + ε := by linarith
    have : 0 < 2 - s := by linarith
    positivity
  have hsup (u : ℝ) : |f u| ≤ kernelSupConst s lam ε * K ^ (lam + ε) :=
    abs_le_kernelSup hs hK hlam hε (by positivity) hf hper hzero hder u
  calc _ ≤ ∑ i ∈ window N K γ, |f (y i / ℓ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ window N K γ, kernelSupConst s lam ε * K ^ (lam + ε) :=
      Finset.sum_le_sum fun i _ => hsup _
    _ = ((window N K γ).card : ℝ) * (kernelSupConst s lam ε * K ^ (lam + ε)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (9 * K ^ γ) * (kernelSupConst s lam ε * K ^ (lam + ε)) :=
      mul_le_mul_of_nonneg_right (card_window_le_of_one_le hK hγ) (by positivity)
    _ = _ := by
      change (9 * K ^ γ) * (kernelSupConst s lam ε * K ^ (lam + ε)) =
        (9 * kernelSupConst s lam ε) * K ^ (γ + lam + ε)
      rw [show γ + lam + ε = γ + (lam + ε) by ring,
        Real.rpow_add hK0 γ (lam + ε)]
      ring

/-- The localized sum at the preceding particle has variance at most
`C K^((κ+1)δ) (K^(2λ)+K^s)`. The constants and smallness threshold
precede `δ`, and the variance coefficient precedes `N, ℓ, f`.
The only hypotheses are the Bakry–Émery criterion `hBE` and the Prékopa–Leindler
inequality `hPL`. -/
theorem a_priori_origin_localized_variance
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 1 < γ) :
    ∃ κ δ₀ : ℝ, 0 < κ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n : ℝ) + 1) * ℓ →
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      f (1 / ℓ / 2) = 0 →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
      let K := ((n : ℝ) + 1) * ℓ
      let T := fun X : Configuration n.succPNat =>
        ∑ i ∈ window n.succPNat K γ, f (originPos X i / ℓ)
      ∃ hT : Integrable T (gibbsMeasure P n.succPNat),
        MemLp T 2 (gibbsMeasure P n.succPNat) ∧
        Riesz1.variance (gibbsMeasure P n.succPNat) T hT ≤
          ENNReal.ofReal (C * K ^ (κ * δ) * (K ^ (2 * lam) + K ^ P.val.2)) := by
  obtain ⟨κ, δ₀, hκ, hδ₀, hb⟩ := a_priori_localized_variance_of_membership
    hBE hPL a_priori_membership_input P lam γ hlam hγ
  refine ⟨κ + 1, δ₀, by linarith, hδ₀, ?_⟩
  intro δ hδ hδδ₀
  obtain ⟨Cl, hCl, hlocal⟩ := hb δ hδ hδδ₀
  obtain ⟨Ct, hCt, htail⟩ := sizeBiasWeight_tail_polynomial (2 * (γ + lam + δ)) δ hδ
  let B := 9 * kernelSupConst P.val.2 lam δ
  refine ⟨Cl + 4 * B ^ 2 * Ct, by positivity, ?_⟩
  intro n hn ℓ hℓ hℓ1 hK f hf hper hzero hder
  let K := ((n : ℝ) + 1) * ℓ
  let μ := gibbsMeasure P n.succPNat
  let μa := μ.map (anchorMap n.succPNat)
  let μr := rotAnchoredLaw P n.succPNat
  have hN : 2 ≤ (n.succPNat : ℕ) := by simpa using hn
  let ν := μr.withDensity (fun y => ENNReal.ofReal (sizeBiasWeight n.succPNat hN y))
  let T := fun y : Fin (n.succPNat : ℕ) → ℝ =>
    ∑ i ∈ window n.succPNat K γ, f (y i / ℓ)
  let L := fun y : Fin n → ℝ => ∑ i ∈ window n.succPNat K γ, f (anchorVector y i / ℓ)
  have hprob : IsProbabilityMeasure μ := isProbabilityMeasure_gibbsMeasure P n.succPNat
  have hproba : IsProbabilityMeasure μa := inferInstanceAs
    (IsProbabilityMeasure (μ.map (anchorMap n.succPNat)))
  have hprobν : IsProbabilityMeasure ν :=
    isProbabilityMeasure_sizeBiased_rotAnchoredLaw P n.succPNat hN
  have hTm : Measurable T := by
    apply Finset.measurable_sum
    intro i _
    have hi : Measurable (fun y : Fin (n.succPNat : ℕ) → ℝ => y i) := measurable_pi_apply i
    exact hf.continuous.measurable.comp (hi.div_const ℓ)
  have hsup (y : Fin (n.succPNat : ℕ) → ℝ) : |T y| ≤ B * K ^ (γ + lam + δ) := by
    simpa only [T, B, K, Nat.succPNat_coe, Nat.cast_succ] using
      origin_localized_abs_le (N := n.succPNat) (ℓ := ℓ) (γ := γ)
      (s := P.val.2) (lam := lam) (ε := δ) hℓ
      (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hK) (by linarith)
      (by linarith [P.2.2.2]) hlam hδ hf hper hzero
      (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hder) y
  have hTr : MemLp T 2 μr := MemLp.of_bound hTm.aestronglyMeasurable _
    (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hsup y)
  have hTν : MemLp T 2 ν := MemLp.of_bound hTm.aestronglyMeasurable _
    (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hsup y)
  obtain ⟨hLi, hL, hLb⟩ := hlocal n hn ℓ hℓ hℓ1 hK f hf hper hzero hder
  have hμa : μa = anchoredLaw P n := by
    change (gibbsMeasure P n.succPNat).map (anchorMap n.succPNat) = _
    rw [show anchorMap n.succPNat =
      (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) from
        funext (anchorMap_eq_anchorCoords n)]
    exact map_snd_gibbsMeasure P n
  have hmap : μa.map anchorVector = μr := by
    rw [hμa]
    exact (rotAnchoredLaw_eq_map_anchorVector P n).symm
  have hL' : MemLp (T ∘ anchorVector) 2 μa := hL
  have hvr : ProbabilityTheory.variance T μr ≤
      Cl * K ^ (κ * δ) * (K ^ (2 * lam) + K ^ P.val.2) := by
    have he := variance_eq_of_map μa μr (measurable_anchorVector n).aemeasurable
      hmap hTr hL'
    have hbr := he.trans_le hLb
    rw [Riesz1.variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
      ← ProbabilityTheory.ofReal_variance hTr] at hbr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbr
  have hνb := variance_sizeBiased_anchored P n.succPNat hN hTm hsup
    (Real.rpow_pos_of_pos (by linarith : 0 < K) δ)
  have hνrate : ProbabilityTheory.variance T ν ≤
      (Cl + 4 * B ^ 2 * Ct) * K ^ ((κ + 1) * δ) * (K ^ (2 * lam) + K ^ P.val.2) := by
    have ht := htail hPL P n.succPNat hN K hK
    have hpow : (K ^ (γ + lam + δ)) ^ 2 = K ^ (2 * (γ + lam + δ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ K)]
      congr 1
      ring
    have hmain : K ^ δ * (Cl * K ^ (κ * δ) * (K ^ (2 * lam) + K ^ P.val.2)) =
        Cl * K ^ ((κ + 1) * δ) * (K ^ (2 * lam) + K ^ P.val.2) := by
      rw [show (κ + 1) * δ = δ + κ * δ by ring,
        Real.rpow_add (by linarith : 0 < K)]
      ring
    have hrate : 1 ≤ K ^ ((κ + 1) * δ) * (K ^ (2 * lam) + K ^ P.val.2) :=
      one_le_a_priori_rate hK (by linarith) hδ.le hlam
    calc ProbabilityTheory.variance T ν ≤ _ := hνb
      _ ≤ K ^ δ * (Cl * K ^ (κ * δ) * (K ^ (2 * lam) + K ^ P.val.2)) +
          4 * (B * K ^ (γ + lam + δ)) ^ 2 *
            (∫ y in {y | K ^ δ < sizeBiasWeight n.succPNat hN y},
              sizeBiasWeight n.succPNat hN y ∂μr) := by
        gcongr
      _ ≤ Cl * K ^ ((κ + 1) * δ) * (K ^ (2 * lam) + K ^ P.val.2) + 4 * B ^ 2 * Ct := by
        rw [hmain, mul_pow, hpow]
        have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ 4 * B ^ 2 by positivity)
        nlinarith only [ht']
      _ ≤ _ := by
        have ht' := mul_le_mul_of_nonneg_left hrate (show 0 ≤ 4 * B ^ 2 * Ct by positivity)
        nlinarith only [ht']
  obtain ⟨hO, hOi, hTi, he⟩ := variance_originPos_eq_sizeBiased P n.succPNat hN hTν
  refine ⟨hOi, hO, he.trans_le ?_⟩
  rw [Riesz1.variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
    ← ProbabilityTheory.ofReal_variance hTν]
  exact ENNReal.ofReal_le_ofReal hνrate

end Riesz1.Internal

end
