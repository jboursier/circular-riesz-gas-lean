/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriAssemblyLocalized
public import Riesz1.Variance.APrioriRotationExteriorTail
public import Riesz1.Variance.APrioriBoundSmallCases

/-!
# Restoring the full anchored sum

The exterior-tail and exponent-choice steps in the proof of Lemma 5.2.
Only the completion-membership proposition `APrioriMembershipInput` is assumed, in addition
to the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset

namespace Riesz1.Internal

/-- Absorb the comparison sum of powers into the final maximum exponent. -/
theorem a_priori_rate_le {K κ δ ε lam s : ℝ} (hK : 1 ≤ K) (hδ : κ * δ ≤ ε) :
    K ^ (κ * δ) * (K ^ (2 * lam) + K ^ s) ≤
      2 * K ^ (ε + max (2 * lam) s) := by
  have hK0 : 0 < K := by linarith
  have h1 : K ^ (κ * δ + 2 * lam) ≤ K ^ (ε + max (2 * lam) s) :=
    Real.rpow_le_rpow_of_exponent_le hK (by linarith [le_max_left (2 * lam) s])
  have h2 : K ^ (κ * δ + s) ≤ K ^ (ε + max (2 * lam) s) :=
    Real.rpow_le_rpow_of_exponent_le hK (by linarith [le_max_right (2 * lam) s])
  rw [mul_add, ← Real.rpow_add hK0, ← Real.rpow_add hK0]
  linarith

/-- The full normalized anchored variance, for all `N ≥ 2`, with the
final exponent of the paper and constants chosen before `N, ℓ, f`.
This is the first assertion of Lemma 5.2 before restoring constants
in the profile and the factor multiplying its derivative. -/
theorem a_priori_anchored_normalized_of_membership
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (hmem : APrioriMembershipInput) (P : Parameters) (lam ε : ℝ)
    (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n : ℝ) + 1) * ℓ →
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      f (1 / ℓ / 2) = 0 →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
      let F := fun X : Configuration n.succPNat =>
        ∑ i, f ((X.val i - X.val ⟨0, n.succPNat.pos⟩) / ℓ)
      ∃ hF : Integrable F (gibbsMeasure P n.succPNat),
        MemLp F 2 (gibbsMeasure P n.succPNat) ∧
        Riesz1.variance (gibbsMeasure P n.succPNat) F hF ≤
          ENNReal.ofReal (C * (((n : ℝ) + 1) * ℓ) ^ (ε + max (2 * lam) P.val.2)) := by
  let γ := (2 - P.val.2) / (1 - P.val.2)
  have hγ : 1 < γ := by
    dsimp [γ]
    rw [lt_div_iff₀ (by linarith [P.2.2.2])]
    linarith
  obtain ⟨κ, ε₀, hκ, hε₀, hl⟩ :=
    a_priori_localized_variance_of_membership hBE hPL hmem P lam γ hlam hγ
  let δ := min ε₀ (ε / κ)
  have hδ : 0 < δ := lt_min hε₀ (div_pos hε hκ)
  have hδ₀ : δ ≤ ε₀ := min_le_left _ _
  have hκδ : κ * δ ≤ ε := by
    have hb := mul_le_mul_of_nonneg_left (min_le_right ε₀ (ε / κ)) hκ.le
    dsimp only [δ]
    nlinarith [div_mul_cancel₀ ε hκ.ne']
  obtain ⟨Cl, hCl, hlocal⟩ := hl δ hδ hδ₀
  obtain ⟨Ce, hCe, hext⟩ := exterior_tail_eLpNorm_le_of_ge P hPL hlam
    (show (0 : ℝ) < 1 by norm_num) (show (2 : ℝ) ≤ 2 by rfl) γ le_rfl
  refine ⟨3 * (Ce ^ 2 + 2 * Cl), by positivity, ?_⟩
  intro n hn ℓ hℓ hℓ1 hK f hf hper hzero hder
  dsimp only
  let K := ((n : ℝ) + 1) * ℓ
  let μ := gibbsMeasure P n.succPNat
  let F := fun X : Configuration n.succPNat =>
    ∑ i, f ((X.val i - X.val ⟨0, n.succPNat.pos⟩) / ℓ)
  let L := fun y : Fin n → ℝ => ∑ j ∈ window n.succPNat K γ, f (anchorVector y j / ℓ)
  let T := L ∘ anchorMap n.succPNat
  have hprob : IsProbabilityMeasure μ := isProbabilityMeasure_gibbsMeasure P n.succPNat
  obtain ⟨hLi, hL, hLb⟩ := hlocal n hn ℓ hℓ hℓ1 hK f hf hper hzero hder
  have hT : MemLp T 2 μ := hL.comp_of_map (measurable_anchorMap n.succPNat).aemeasurable
  have hF : MemLp F 2 μ := by
    apply memLp_finsetSum
    intro i _
    have hm : Measurable (fun X : Configuration n.succPNat =>
        f ((X.val i - X.val ⟨0, n.succPNat.pos⟩) / ℓ)) := by
      have hx (j : Fin (n.succPNat : ℕ)) :
          Measurable (fun X : Configuration n.succPNat => X.val j) :=
        (measurable_pi_apply j).comp measurable_subtype_coe
      apply hf.continuous.measurable.comp
      exact ((hx i).sub (hx ⟨0, n.succPNat.pos⟩)).div_const ℓ
    have hsup := abs_le_kernelSup (s := P.val.2) (lam := lam) (ε := δ)
      (by linarith [P.2.2.2]) hK hlam hδ (by positivity) hf hper hzero hder
    exact MemLp.of_bound hm.aestronglyMeasurable _
      (ae_of_all _ fun X => by simpa only [Real.norm_eq_abs] using hsup _)
  have hTb : Riesz1.variance μ T (hT.integrable one_le_two) ≤
      ENNReal.ofReal (2 * Cl * K ^ (ε + max (2 * lam) P.val.2)) := by
    have hm := variance_map_eq μ (measurable_anchorMap n.succPNat).aemeasurable hL
    change Riesz1.variance _ L _ = Riesz1.variance μ T _ at hm
    rw [← hm]
    apply hLb.trans (ENNReal.ofReal_le_ofReal _)
    have hb := mul_le_mul_of_nonneg_left
      (a_priori_rate_le (lam := lam) (s := P.val.2) hK hκδ) hCl.le
    dsimp only [K] at hb ⊢
    nlinarith only [hb]
  have hextb := hext n.succPNat ℓ (by simpa using hn) hℓ hℓ1
    (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hK) f hf hper hzero
    (by simpa only [cutoffMajorant, majorantNear, majorantFar, Nat.succPNat_coe, Nat.cast_succ] using hder)
  have hdiff : (fun X => F X - T X - 0) = exteriorSum n.succPNat ℓ γ f := by
    funext X
    have hcoords := APrioriComparison.anchorVector_anchorMap n X
    have hsum := Finset.sum_add_sum_compl (window n.succPNat K γ)
      (fun i => f ((X.val i - X.val ⟨0, n.succPNat.pos⟩) / ℓ))
    change (∑ i, f ((X.val i - X.val ⟨0, n.succPNat.pos⟩) / ℓ)) -
      (∑ j ∈ window n.succPNat K γ,
        f (anchorVector (anchorMap n.succPNat X) j / ℓ)) - 0 = _
    rw [hcoords]
    have he : exteriorSum n.succPNat ℓ γ f X =
        ∑ i ∈ (window n.succPNat K γ)ᶜ,
          f ((X.val i - X.val ⟨0, n.succPNat.pos⟩) / ℓ) := by
      unfold exteriorSum
      simp only [Nat.succPNat_coe, Nat.cast_succ]
      change (∑ i ∈ (window n.succPNat K γ)ᶜ,
        f ((cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ)) = _
      apply Finset.sum_congr rfl
      intro i _
      rw [cyclicLift_natCast X i, cyclicLift_zero]
      rfl
    rw [he]
    linarith only [hsum]
  have hv := variance_le_two_errors μ hF hT hT 0
  have hz : eLpNorm (fun _ : Configuration n.succPNat => (0 : ℝ)) 2 μ = 0 := eLpNorm_zero
  simp only [sub_self, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hv
  rw [hdiff] at hv
  refine ⟨hF.integrable one_le_two, hF, hv.trans ?_⟩
  have hKpow : 1 ≤ K ^ (ε + max (2 * lam) P.val.2) :=
    Real.one_le_rpow hK (by linarith [le_max_left (2 * lam) P.val.2])
  calc _ ≤ 3 * (ENNReal.ofReal Ce ^ 2 +
        ENNReal.ofReal (2 * Cl * K ^ (ε + max (2 * lam) P.val.2))) := by
          norm_num only [ENNReal.ofReal_ofNat] at hextb
          gcongr
    _ = ENNReal.ofReal (3 * (Ce ^ 2 + 2 * Cl * K ^ (ε + max (2 * lam) P.val.2))) := by
        rw [← ENNReal.ofReal_pow hCe, ← ENNReal.ofReal_add (sq_nonneg _) (by positivity),
          ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hb := le_mul_of_one_le_right (sq_nonneg Ce) hKpow
        dsimp only [K] at hb ⊢
        nlinarith only [hb]

end Riesz1.Internal

end
