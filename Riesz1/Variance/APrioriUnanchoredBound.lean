/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriUnanchoredLocalized
public import Riesz1.Variance.APrioriRotationTranslationL2

/-!
# The normalized spatial-origin a priori variance

The unanchored assertion of Lemma 5.2, before restoring
an additive constant and the factor multiplying the derivative envelope.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset

namespace Riesz1.Internal

/-- Internal assembly at fixed scale: the three quantitative inputs are
supplied by the preceding-particle variance and the two rotation estimates. -/
theorem a_priori_unanchored_normalized_at
    (P : Parameters) (lam ε γ κ c δ Cl Ct Ce : ℝ)
    (hlam : 0 ≤ lam) (hε : 0 < ε) (hγ : 1 < γ) (hδ : 0 < δ)
    (hCl : 0 < Cl) (hCt : 0 ≤ Ct) (_hCe : 0 ≤ Ce)
    (hκδ : κ * δ ≤ ε) (hcδ : c * δ ≤ ε)
    (n : ℕ) (hn : 1 ≤ n) (ℓ : ℝ) (hℓ : 0 < ℓ) (hK : 1 ≤ ((n : ℝ) + 1) * ℓ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f (1 / ℓ))
    (hzero : f (1 / ℓ / 2) = 0)
    (hder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|)
    (hlocal : ∃ hT : Integrable (fun X : Configuration n.succPNat =>
        ∑ i ∈ window n.succPNat (((n : ℝ) + 1) * ℓ) γ, f (originPos X i / ℓ))
          (gibbsMeasure P n.succPNat),
      MemLp (fun X : Configuration n.succPNat =>
        ∑ i ∈ window n.succPNat (((n : ℝ) + 1) * ℓ) γ, f (originPos X i / ℓ)) 2
          (gibbsMeasure P n.succPNat) ∧
      Riesz1.variance (gibbsMeasure P n.succPNat) _ hT ≤
        ENNReal.ofReal (Cl * (((n : ℝ) + 1) * ℓ) ^ (κ * δ) *
          ((((n : ℝ) + 1) * ℓ) ^ (2 * lam) + (((n : ℝ) + 1) * ℓ) ^ P.val.2)))
    (hext : ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight n.succPNat (by simpa using hn) y),
      ENNReal.ofReal (jointExteriorSum n.succPNat ℓ γ f D y ^ 2))
        ∂rotAnchoredLaw P n.succPNat ≤ ENNReal.ofReal (Ce ^ 2))
    (htrans : ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight n.succPNat (by simpa using hn) y),
      ENNReal.ofReal (translationError n.succPNat ℓ γ f D y ^ 2))
        ∂rotAnchoredLaw P n.succPNat ≤
      ENNReal.ofReal (Ct * (((n : ℝ) + 1) * ℓ) ^ (c * δ) *
        (1 + (((n : ℝ) + 1) * ℓ) ^ (2 * lam)))) :
    ∃ hF : Integrable (fun X : Configuration n.succPNat => ∑ i, f (X.val i / ℓ))
        (gibbsMeasure P n.succPNat),
      MemLp (fun X : Configuration n.succPNat => ∑ i, f (X.val i / ℓ)) 2
        (gibbsMeasure P n.succPNat) ∧
      Riesz1.variance (gibbsMeasure P n.succPNat) _ hF ≤
        ENNReal.ofReal ((3 * (Ce ^ 2 + 2 * Ct + 2 * Cl)) *
          (((n : ℝ) + 1) * ℓ) ^ (ε + max (2 * lam) P.val.2)) := by
  let K := ((n : ℝ) + 1) * ℓ
  let μ := gibbsMeasure P n.succPNat
  let F := fun X : Configuration n.succPNat => ∑ i, f (X.val i / ℓ)
  let T := fun X : Configuration n.succPNat =>
    ∑ i ∈ window n.succPNat K γ, f (originPos X i / ℓ)
  let Δ := fun X : Configuration n.succPNat =>
    translationError n.succPNat ℓ γ f (originD X) (originPos X)
  let E := fun X : Configuration n.succPNat =>
    jointExteriorSum n.succPNat ℓ γ f (originD X) (originPos X)
  have hN : 2 ≤ (n.succPNat : ℕ) := by simpa using hn
  have hKN : 1 ≤ (n.succPNat : ℝ) * ℓ := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hK
  have hderN : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ cutoffMajorant P.val.2 lam ((n.succPNat : ℝ) * ℓ) |u| := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hder
  have hprob : IsProbabilityMeasure μ := isProbabilityMeasure_gibbsMeasure P n.succPNat
  obtain ⟨hTi, hT, hTb⟩ := hlocal
  have hΔcont : Continuous (fun p : ℝ × (Fin (n.succPNat : ℕ) → ℝ) =>
      translationError n.succPNat ℓ γ f p.1 p.2) := by
    unfold translationError
    apply Continuous.sub
    · apply continuous_finsetSum
      intro i _
      have hi : Continuous (fun p : ℝ × (Fin (n.succPNat : ℕ) → ℝ) => p.2 i) :=
        (continuous_apply i).comp continuous_snd
      exact hf.continuous.comp (((continuous_const.mul hi).sub continuous_fst).div_const _)
    · apply continuous_finsetSum
      intro i _
      have hi : Continuous (fun p : ℝ × (Fin (n.succPNat : ℕ) → ℝ) => p.2 i) :=
        (continuous_apply i).comp continuous_snd
      exact hf.continuous.comp (hi.div_const ℓ)
  have hpair : Measurable (fun X : Configuration n.succPNat => (originD X, originPos X)) :=
    (measurable_originD n.succPNat).prodMk (measurable_originPos n.succPNat)
  have hΔm : Measurable Δ := by
    have hm := hΔcont.measurable.comp hpair
    exact hm
  have hEm : Measurable E := by
    have hm :=
      (continuous_jointExteriorSum (N := n.succPNat) ℓ γ hf.continuous).measurable.comp hpair
    exact hm
  have hF : MemLp F 2 μ := by
    apply memLp_finsetSum
    intro i _
    have hi : Measurable (fun X : Configuration n.succPNat => X.val i / ℓ) :=
      by
        have hx : Measurable (fun X : Configuration n.succPNat => X.val i) :=
          (measurable_pi_apply i).comp measurable_subtype_coe
        exact hx.div_const ℓ
    apply MemLp.of_bound (hf.continuous.measurable.comp hi).aestronglyMeasurable
      (kernelSupConst P.val.2 lam δ * K ^ (lam + δ))
    exact ae_of_all _ fun X => by
      simpa only [Real.norm_eq_abs, Function.comp_def, K] using abs_le_kernelSup (by linarith [P.2.2.2])
        hK hlam hδ (by positivity) hf hper hzero hder (X.val i / ℓ)
  have hΔ : MemLp Δ 2 μ := by
    apply MemLp.of_bound hΔm.aestronglyMeasurable
      (2 * (9 * ((n.succPNat : ℝ) * ℓ) ^ γ) *
        (kernelSupConst P.val.2 lam δ * ((n.succPNat : ℝ) * ℓ) ^ (lam + δ)))
    exact ae_of_all _ fun X => by
      simpa only [Real.norm_eq_abs] using abs_translationError_le_uniform n.succPNat
        (by linarith [P.2.2.2]) hKN (by linarith) hlam hδ hℓ hf hper hzero hderN
        (originD X) (originPos X)
  have heq (X : Configuration n.succPNat) : F X = T X + Δ X + E X := by
    simpa only [F, T, Δ, E, K, Nat.succPNat_coe, Nat.cast_succ] using
      plain_sum_eq_origin_decomposition hℓ.ne' γ hper X
  have hEb : (∫⁻ X, ENNReal.ofReal (E X ^ 2) ∂μ) ≤ ENNReal.ofReal (Ce ^ 2) := by
    rw [show (∫⁻ X, ENNReal.ofReal (E X ^ 2) ∂μ) =
      ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight n.succPNat hN y),
        ENNReal.ofReal (jointExteriorSum n.succPNat ℓ γ f D y ^ 2))
          ∂rotAnchoredLaw P n.succPNat from
      lintegral_jointExteriorSum_sq_gibbs P hN ℓ γ hf.continuous]
    exact hext
  have hΔb : (∫⁻ X, ENNReal.ofReal (Δ X ^ 2) ∂μ) ≤
      ENNReal.ofReal (Ct * K ^ (c * δ) * (1 + K ^ (2 * lam))) := by
    have hj := joint_law_rotAnchoredLaw P n.succPNat hN
      (fun D y => ENNReal.ofReal (translationError n.succPNat ℓ γ f D y ^ 2))
      (ENNReal.measurable_ofReal.comp (hΔcont.measurable.pow_const 2))
    change (∫⁻ X, ENNReal.ofReal (Δ X ^ 2) ∂μ) = _ at hj
    rw [hj]
    exact htrans
  let Q := K ^ (ε + max (2 * lam) P.val.2)
  have hQ : 1 ≤ Q := Real.one_le_rpow hK
    (by linarith [le_max_left (2 * lam) P.val.2])
  have hTl : Riesz1.variance μ T hTi ≤ ENNReal.ofReal (2 * Cl * Q) := by
    apply hTb.trans (ENNReal.ofReal_le_ofReal _)
    have hb := mul_le_mul_of_nonneg_left
      (a_priori_rate_le (lam := lam) (s := P.val.2) hK hκδ) hCl.le
    nlinarith only [hb]
  have hΔl : (∫⁻ X, ENNReal.ofReal (Δ X ^ 2) ∂μ) ≤ ENNReal.ofReal (2 * Ct * Q) := by
    apply hΔb.trans (ENNReal.ofReal_le_ofReal _)
    have hs : 1 ≤ K ^ P.val.2 := Real.one_le_rpow hK P.2.2.1.le
    have hpow : K ^ (c * δ) * (1 + K ^ (2 * lam)) ≤
        K ^ (c * δ) * (K ^ (2 * lam) + K ^ P.val.2) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hb := hpow.trans (a_priori_rate_le (lam := lam) (s := P.val.2) hK hcδ)
    have hm := mul_le_mul_of_nonneg_left hb hCt
    nlinarith only [hm]
  have hv := variance_le_two_errors μ hF (hT.add hΔ) hT 0
  change Riesz1.variance μ F _ ≤ 3 *
    (eLpNorm (fun X => F X - (T X + Δ X) - 0) 2 μ ^ 2 +
      eLpNorm (fun X => T X + Δ X - T X) 2 μ ^ 2 + Riesz1.variance μ T _) at hv
  have he1 : (fun X => F X - (T X + Δ X) - 0) = E := by
    funext X
    linarith only [heq X]
  have he2 : (fun X => T X + Δ X - T X) = Δ := by funext X; ring
  rw [he1, he2, ← lintegral_sq_eq_eLpNorm_two_sq hEm.aestronglyMeasurable,
    ← lintegral_sq_eq_eLpNorm_two_sq hΔm.aestronglyMeasurable] at hv
  refine ⟨hF.integrable one_le_two, hF, hv.trans ?_⟩
  calc _ ≤ 3 * (ENNReal.ofReal (Ce ^ 2) + ENNReal.ofReal (2 * Ct * Q) +
      ENNReal.ofReal (2 * Cl * Q)) := by gcongr
    _ = ENNReal.ofReal (3 * (Ce ^ 2 + 2 * Ct * Q + 2 * Cl * Q)) := by
      rw [← ENNReal.ofReal_add (sq_nonneg _) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hb := mul_le_mul_of_nonneg_left hQ (sq_nonneg Ce)
      change 3 * (Ce ^ 2 + 2 * Ct * Q + 2 * Cl * Q) ≤
        3 * (Ce ^ 2 + 2 * Ct + 2 * Cl) * Q
      nlinarith only [hb]

/-- The full plain sum, with a normalized test function, has the exponent
of the paper. Both error moments use the actual joint origin law. -/
theorem a_priori_unanchored_normalized
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n : ℝ) + 1) * ℓ →
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      f (1 / ℓ / 2) = 0 →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
      let F := fun X : Configuration n.succPNat => ∑ i, f (X.val i / ℓ)
      ∃ hF : Integrable F (gibbsMeasure P n.succPNat),
        MemLp F 2 (gibbsMeasure P n.succPNat) ∧
        Riesz1.variance (gibbsMeasure P n.succPNat) F hF ≤
          ENNReal.ofReal (C * (((n : ℝ) + 1) * ℓ) ^ (ε + max (2 * lam) P.val.2)) := by
  let γ := (2 - P.val.2) / (1 - P.val.2)
  have hγ : 1 < γ := by
    dsimp [γ]
    rw [lt_div_iff₀ (by linarith [P.2.2.2])]
    linarith
  obtain ⟨κ, δ₀, hκ, hδ₀, hl⟩ :=
    a_priori_origin_localized_variance hBE hPL P lam γ hlam hγ
  obtain ⟨c, hc, ht⟩ := translation_lintegral_sq_le P hBE hPL hlam hγ
  let δ := min δ₀ (min (ε / κ) (ε / c))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (div_pos hε hκ) (div_pos hε hc))
  have hκδ : κ * δ ≤ ε := by
    have hd : δ ≤ ε / κ := (min_le_right _ _).trans (min_le_left _ _)
    have hm := (le_div_iff₀ hκ).mp hd
    simpa only [mul_comm] using hm
  have hcδ : c * δ ≤ ε := by
    have hd : δ ≤ ε / c := (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ hc).mp hd
    simpa only [mul_comm] using hm
  obtain ⟨Cl, hCl, hlocal⟩ := hl δ hδ (min_le_left _ _)
  obtain ⟨Ct, hCt, htrans⟩ := ht δ hδ
  obtain ⟨Ce, hCe, hext⟩ := jointExteriorSum_lintegral_sq_le_of_ge P hPL hlam hδ γ le_rfl
  refine ⟨3 * (Ce ^ 2 + 2 * Ct + 2 * Cl), by positivity, ?_⟩
  intro n hn ℓ hℓ hℓ1 hK f hf hper hzero hder
  have hN : 2 ≤ (n.succPNat : ℕ) := by simpa using hn
  have hKN : 1 ≤ (n.succPNat : ℝ) * ℓ := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hK
  have hderN : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ (if |u| ≤ 2 then
          1 / (max |u| ((n.succPNat : ℝ) * ℓ)⁻¹) ^ (1 + lam) else 0) +
        (if 2 ≤ |u| then 1 / |u| ^ (3 - P.val.2) else 0) := by
    simpa only [cutoffMajorant, majorantNear, majorantFar,
      Nat.succPNat_coe, Nat.cast_succ] using hder
  apply a_priori_unanchored_normalized_at P lam ε γ κ c δ Cl Ct Ce
    hlam hε hγ hδ hCl hCt hCe hκδ hcδ n hn ℓ hℓ hK f hf hper hzero hder
    (hlocal n hn ℓ hℓ hℓ1 hK f hf hper hzero hder)
  · exact hext n.succPNat ℓ hN hℓ hℓ1 hKN f hf hper hzero hderN
  · simpa only [Nat.succPNat_coe, Nat.cast_succ] using
      htrans n.succPNat ℓ hN hℓ hℓ1 hKN f hf hper hzero hderN

end Riesz1.Internal

end
