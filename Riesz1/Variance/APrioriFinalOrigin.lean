/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriUnanchoredScaling
public import Riesz1.Variance.APrioriTranslateRadius
public import Riesz1.Bridges.InputConsolidation

/-!
# Both a priori variances at the original centre

Both variance bounds of the a priori lemma at centre zero, for every particle number, the factor
`M²`, and every positive fixed radius. The radius-two case is the lemma itself. A radius at most
two is reduced to it by a comparison of envelopes. A larger radius `2a` is reduced to it by the
dilation of the observation length by `a`, when the dilated length is at most one. Otherwise the
observation length is at least one, and the dilation onto the unit circle gives the macroscopic
case. The translated anchored envelope is a separate assertion and is not claimed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Both bounds of the a priori lemma at radius two and centre zero, with the factor `M²`. -/
theorem a_priori_original (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ,
      ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ M * cutoffMajorant P.val.2 lam ((N : ℝ) * ℓ) |u|) →
      (∃ hA : Integrable (fun X : Configuration N =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) hA ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) ∧
      (∃ hB : Integrable (fun X : Configuration N => ∑ i, f (X.val i / ℓ)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X => ∑ i, f (X.val i / ℓ)) hB ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) := by
  obtain ⟨Ca, hCa, ha⟩ := Internal.a_priori_anchored hBE hPL P lam ε hlam hε
  obtain ⟨Cb, hCb, hb⟩ := Internal.a_priori_unanchored hBE hPL P lam ε hlam hε
  refine ⟨Ca + Cb, add_pos hCa hCb, ?_⟩
  intro N ℓ hℓ hℓ1 hK M hM f hf hper hder
  have hm : 0 ≤ M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2) := by positivity
  constructor
  · obtain ⟨hA, hv⟩ := ha N ℓ hℓ hℓ1 hK M hM f hf hper hder
    refine ⟨hA, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have h := mul_le_mul_of_nonneg_right (show Ca ≤ Ca + Cb by linarith) hm
    simpa only [mul_assoc] using h
  · obtain ⟨hB, hv⟩ := hb N ℓ hℓ hℓ1 hK M hM f hf hper hder
    refine ⟨hB, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have h := mul_le_mul_of_nonneg_right (show Cb ≤ Ca + Cb by linarith) hm
    simpa only [mul_assoc] using h

/-- Transports a variance bound along an equality of the summands. -/
theorem exists_variance_of_summands_eq (P : Parameters) (N : ℕ+) {F G : Configuration N → ℝ}
    (h : F = G) (hG : Integrable G (gibbsMeasure P N)) {b : ENNReal}
    (hb : variance (gibbsMeasure P N) G hG ≤ b) :
    ∃ hF : Integrable F (gibbsMeasure P N), variance (gibbsMeasure P N) F hF ≤ b := by
  subst h
  exact ⟨hG, hb⟩

/-- Both bounds of the a priori lemma for every positive fixed radius, at centre zero. The
constant is chosen before `N, ℓ, M, f`. A radius at most two is compared with radius two. A
radius `2a` with `a ≥ 1` is reduced to radius two by the dilation by `a`, when `aℓ ≤ 1`, and to
the unit circle otherwise. -/
theorem a_priori_at_origin (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε R : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ,
      ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ M * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ) R |u|) →
      (∃ hA : Integrable (fun X : Configuration N =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) hA ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) ∧
      (∃ hB : Integrable (fun X : Configuration N => ∑ i, f (X.val i / ℓ)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X => ∑ i, f (X.val i / ℓ)) hB ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) := by
  obtain ⟨C, hC, hb⟩ := a_priori_original hBE hPL P lam ε hlam hε
  have hs : P.val.2 < 3 := by linarith [P.2.2.2]
  have hp : 0 ≤ ε + max (2 * lam) P.val.2 := by
    have := le_max_left (2 * lam) P.val.2
    linarith
  rcases le_total R 2 with hR2 | hR2
  · -- A radius at most two: the envelope is dominated by the radius-two envelope.
    have hB : 0 < 1 + 2 ^ (1 + lam) * R ^ (P.val.2 - 3) := by
      have := mul_nonneg (Real.rpow_nonneg zero_le_two (1 + lam))
        (Real.rpow_nonneg hR.le (P.val.2 - 3))
      linarith
    refine ⟨C * (1 + 2 ^ (1 + lam) * R ^ (P.val.2 - 3)) ^ 2, mul_pos hC (pow_pos hB 2), ?_⟩
    intro N ℓ hℓ hℓ1 hK M hM f hf hper hder
    have hd : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ (M * (1 + 2 ^ (1 + lam) * R ^ (P.val.2 - 3))) *
          cutoffMajorant P.val.2 lam ((N : ℝ) * ℓ) |u| := by
      intro u hu
      apply (hder u hu).trans
      rw [Internal.cutoffMajorant_eq_aPrioriEnvelope, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (Internal.aPrioriEnvelope_le_two_of_le hs hlam hR hR2 hK (abs_nonneg u)) hM
    obtain ⟨⟨hAi, hAv⟩, ⟨hBi, hBv⟩⟩ :=
      hb N ℓ hℓ hℓ1 hK _ (mul_nonneg hM hB.le) f hf hper hd
    have he : C * (M * (1 + 2 ^ (1 + lam) * R ^ (P.val.2 - 3))) ^ 2 =
        C * (1 + 2 ^ (1 + lam) * R ^ (P.val.2 - 3)) ^ 2 * M ^ 2 := by ring
    exact ⟨⟨hAi, by simpa only [he] using hAv⟩, ⟨hBi, by simpa only [he] using hBv⟩⟩
  · -- A radius `2a` with `a ≥ 1`: the dilation by `a` is admissible at every scale `Nℓ ≥ 1`.
    obtain ⟨a, rfl⟩ : ∃ a, R = 2 * a := ⟨R / 2, by ring⟩
    have ha : 0 < a := by linarith
    have ha1 : 1 ≤ a := by linarith
    set Ca := a ^ (-lam) + a ^ (P.val.2 - 2) with hCa_def
    have hCa0 : 0 < Ca := by
      rw [hCa_def]
      exact add_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos ha _)
    have hD : 0 < (1 + Ca ^ 2) * a ^ (ε + max (2 * lam) P.val.2) :=
      mul_pos (by positivity) (Real.rpow_pos_of_pos ha _)
    refine ⟨C * ((1 + Ca ^ 2) * a ^ (ε + max (2 * lam) P.val.2)), mul_pos hC hD, ?_⟩
    intro N ℓ hℓ hℓ1 hK M hM f hf hper hder
    have hNℓ : 0 < (N : ℝ) * ℓ := by linarith
    have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr N.pos
    have hNpos : (0 : ℝ) < N := by linarith
    by_cases hlen : a * ℓ ≤ 1
    · -- The dilated length `aℓ` is at most one, so the rescaled function satisfies the a priori
      -- lemma at scale `aℓ`, with the envelope of radius two at the scale `aNℓ`.
      have hg : ContDiff ℝ 1 (fun v : ℝ => f (a * v)) :=
        hf.comp (contDiff_const.mul contDiff_id)
      have hgper : Function.Periodic (fun v : ℝ => f (a * v)) (1 / (a * ℓ)) := by
        intro v
        show f (a * (v + 1 / (a * ℓ))) = f (a * v)
        rw [show a * (v + 1 / (a * ℓ)) = a * v + 1 / ℓ by field_simp]
        exact hper (a * v)
      have hgd : ∀ u ∈ Icc (-(1 / (a * ℓ) / 2)) (1 / (a * ℓ) / 2),
          |deriv (fun v : ℝ => f (a * v)) u| ≤
            (M * Ca) * cutoffMajorant P.val.2 lam ((N : ℝ) * (a * ℓ)) |u| := by
        intro u hu
        have hhalf : a * (1 / (a * ℓ) / 2) = 1 / ℓ / 2 := by field_simp
        have hau : a * u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2) := by
          constructor
          · have h1 := mul_le_mul_of_nonneg_left hu.1 ha.le
            rw [mul_neg, hhalf] at h1
            exact h1
          · have h2 := mul_le_mul_of_nonneg_left hu.2 ha.le
            rw [hhalf] at h2
            exact h2
        have habs : |a * u| = a * |u| := by rw [abs_mul, abs_of_pos ha]
        have hd := hder (a * u) hau
        rw [habs] at hd
        have hd' : |deriv (fun v : ℝ => f (a * v)) u| = a * |deriv f (a * u)| := by
          rw [deriv_comp_mul_left, smul_eq_mul, abs_mul, abs_of_pos ha]
        rw [hd', show (N : ℝ) * (a * ℓ) = a * ((N : ℝ) * ℓ) by ring,
          Internal.cutoffMajorant_eq_aPrioriEnvelope]
        calc a * |deriv f (a * u)|
            ≤ a * (M * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ) (2 * a) (a * |u|)) :=
              mul_le_mul_of_nonneg_left hd ha.le
          _ = M * (a * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ) (2 * a) (a * |u|)) := by
              ring
          _ ≤ M * (Ca * Internal.aPrioriEnvelope P.val.2 lam (a * ((N : ℝ) * ℓ)) 2 |u|) :=
              mul_le_mul_of_nonneg_left (Internal.aPrioriEnvelope_dilate ha hNℓ) hM
          _ = (M * Ca) * Internal.aPrioriEnvelope P.val.2 lam (a * ((N : ℝ) * ℓ)) 2 |u| := by
              ring
      have hsideA : (1 : ℝ) ≤ (N : ℝ) * (a * ℓ) := by
        rw [show (N : ℝ) * (a * ℓ) = a * ((N : ℝ) * ℓ) by ring]
        nlinarith
      obtain ⟨⟨hAi, hAv⟩, ⟨hBi, hBv⟩⟩ :=
        hb N (a * ℓ) (mul_pos ha hℓ) hlen hsideA (M * Ca) (mul_nonneg hM hCa0.le) _ hg hgper hgd
      have hreal : C * (M * Ca) ^ 2 * ((N : ℝ) * (a * ℓ)) ^ (ε + max (2 * lam) P.val.2) ≤
          C * ((1 + Ca ^ 2) * a ^ (ε + max (2 * lam) P.val.2)) * M ^ 2 *
            ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2) := by
        rw [show (N : ℝ) * (a * ℓ) = a * ((N : ℝ) * ℓ) by ring,
          Real.mul_rpow ha.le hNℓ.le]
        have hnn : 0 ≤ C * M ^ 2 * a ^ (ε + max (2 * lam) P.val.2) *
            ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2) :=
          mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg M)) (Real.rpow_nonneg ha.le _))
            (Real.rpow_nonneg hNℓ.le _)
        nlinarith [hnn]
      have hfA : (fun X : Configuration N => ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) =
          (fun X : Configuration N =>
            ∑ i, (fun v : ℝ => f (a * v)) ((X.val i - X.val ⟨0, N.pos⟩) / (a * ℓ))) := by
        funext X
        refine Finset.sum_congr rfl fun i _ => ?_
        show f _ = f (a * _)
        congr 1
        rw [← mul_div_assoc, mul_div_mul_left _ _ ha.ne']
      have hfB : (fun X : Configuration N => ∑ i, f (X.val i / ℓ)) =
          (fun X : Configuration N => ∑ i, (fun v : ℝ => f (a * v)) (X.val i / (a * ℓ))) := by
        funext X
        refine Finset.sum_congr rfl fun i _ => ?_
        show f _ = f (a * _)
        congr 1
        rw [← mul_div_assoc, mul_div_mul_left _ _ ha.ne']
      exact ⟨exists_variance_of_summands_eq P N hfA hAi (hAv.trans (ENNReal.ofReal_le_ofReal hreal)),
        exists_variance_of_summands_eq P N hfB hBi (hBv.trans (ENNReal.ofReal_le_ofReal hreal))⟩
    · -- The dilated length exceeds one, so `ℓ > 1/a`. The function `v ↦ f(v/ℓ)` lives on the
      -- unit circle, and its derivative has the near term only, which is the macroscopic case.
      have hlen' : 1 < a * ℓ := lt_of_not_ge hlen
      have hℓinv : 0 < 1 / ℓ := by positivity
      have hg : ContDiff ℝ 1 (fun v : ℝ => f (1 / ℓ * v)) :=
        hf.comp (contDiff_const.mul contDiff_id)
      have hgper : Function.Periodic (fun v : ℝ => f (1 / ℓ * v)) (1 / 1) := by
        intro v
        show f (1 / ℓ * (v + 1 / 1)) = f (1 / ℓ * v)
        rw [show 1 / ℓ * (v + 1 / 1) = 1 / ℓ * v + 1 / ℓ by ring]
        exact hper _
      have hgd : ∀ u ∈ Icc (-(1 / 1 / 2)) (1 / 1 / 2),
          |deriv (fun v : ℝ => f (1 / ℓ * v)) u| ≤
            M * cutoffMajorant P.val.2 lam ((N : ℝ) * 1) |u| := by
        intro u hu
        have hu2 : |u| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have habs : |1 / ℓ * u| = 1 / ℓ * |u| := by rw [abs_mul, abs_of_pos hℓinv]
        have ht : 1 / ℓ * u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2) := by
          have h2 : |1 / ℓ * u| ≤ 1 / ℓ / 2 := by
            rw [habs]
            have h3 := mul_le_mul_of_nonneg_left hu2 hℓinv.le
            rw [show 1 / ℓ * (1 / 2) = 1 / ℓ / 2 by ring] at h3
            exact h3
          exact abs_le.1 h2
        have hd := hder (1 / ℓ * u) ht
        rw [habs] at hd
        have hd' : |deriv (fun v : ℝ => f (1 / ℓ * v)) u| = 1 / ℓ * |deriv f (1 / ℓ * u)| := by
          rw [deriv_comp_mul_left, smul_eq_mul, abs_mul, abs_of_pos hℓinv]
        have hdR : |u| < ℓ * (2 * a) := by
          have : ℓ * (2 * a) = 2 * (a * ℓ) := by ring
          rw [this]
          linarith
        have hd2 : |u| ≤ 2 := hu2.trans (by norm_num)
        rw [hd', Internal.cutoffMajorant_eq_aPrioriEnvelope]
        calc 1 / ℓ * |deriv f (1 / ℓ * u)|
            ≤ 1 / ℓ * (M * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ) (2 * a)
                (1 / ℓ * |u|)) := mul_le_mul_of_nonneg_left hd hℓinv.le
          _ = M * (1 / ℓ * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ) (2 * a)
                (1 / ℓ * |u|)) := by
              ring
          _ ≤ M * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * 1) 2 |u| := by
              apply mul_le_mul_of_nonneg_left _ hM
              have key := Internal.aPrioriEnvelope_unit (s := P.val.2) (lam := lam) hℓ hℓ1 hlam
                hNpos hd2 hdR
              simpa only [one_div, mul_one] using key
      have hsideM : (1 : ℝ) ≤ (N : ℝ) * 1 := by rw [mul_one]; exact hN1
      obtain ⟨⟨hAi, hAv⟩, ⟨hBi, hBv⟩⟩ :=
        hb N 1 zero_lt_one le_rfl hsideM M hM _ hg hgper hgd
      have hNle : (N : ℝ) * 1 ≤ a * ((N : ℝ) * ℓ) := by
        rw [mul_one, show a * ((N : ℝ) * ℓ) = (N : ℝ) * (a * ℓ) by ring]
        nlinarith
      have hreal : C * M ^ 2 * ((N : ℝ) * 1) ^ (ε + max (2 * lam) P.val.2) ≤
          C * ((1 + Ca ^ 2) * a ^ (ε + max (2 * lam) P.val.2)) * M ^ 2 *
            ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2) := by
        have h1 : ((N : ℝ) * 1) ^ (ε + max (2 * lam) P.val.2) ≤
            (a * ((N : ℝ) * ℓ)) ^ (ε + max (2 * lam) P.val.2) :=
          Real.rpow_le_rpow (by positivity) hNle hp
        rw [Real.mul_rpow ha.le hNℓ.le] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC.le (sq_nonneg M))
        have h3 : 0 ≤ C * M ^ 2 * Ca ^ 2 * (a ^ (ε + max (2 * lam) P.val.2) *
            ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2)) :=
          mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg M)) (sq_nonneg Ca))
            (mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hNℓ.le _))
        nlinarith [h2, h3]
      have hfA : (fun X : Configuration N => ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) =
          (fun X : Configuration N =>
            ∑ i, (fun v : ℝ => f (1 / ℓ * v)) ((X.val i - X.val ⟨0, N.pos⟩) / 1)) := by
        funext X
        refine Finset.sum_congr rfl fun i _ => ?_
        show f _ = f (1 / ℓ * _)
        congr 1
        ring
      have hfB : (fun X : Configuration N => ∑ i, f (X.val i / ℓ)) =
          (fun X : Configuration N => ∑ i, (fun v : ℝ => f (1 / ℓ * v)) (X.val i / 1)) := by
        funext X
        refine Finset.sum_congr rfl fun i _ => ?_
        show f _ = f (1 / ℓ * _)
        congr 1
        ring
      exact ⟨exists_variance_of_summands_eq P N hfA hAi (hAv.trans (ENNReal.ofReal_le_ofReal hreal)),
        exists_variance_of_summands_eq P N hfB hBi (hBv.trans (ENNReal.ofReal_le_ofReal hreal))⟩

end Riesz1

end
